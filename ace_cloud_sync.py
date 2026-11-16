# -*- coding: utf-8 -*-
"""
MÓDULO DE SINCRONIZACIÓN EN TIEMPO REAL EN LA NUBE (OPCIÓN B - SUPABASE REST / POSTGRES)
(c) SERVICIOS TECNOLOGICOS AI, SL 2026
Permite que el PC (Windows) y los dispositivos móviles (Android 10+ / iOS) compartan en tiempo real:
  - El estado exacto del trabajador (fichar ENTRADA en el móvil y SALIDA en el PC o viceversa).
  - La cadena inalterable de hashes HMAC-SHA256 sin colisiones concurrentes (vía RPC atómico o caché local).
  - Las consultas del trabajador ("Mis Registros" y "Resumen Mensual" art. 35.5 ET) y del Administrador.
  - Descubrimiento automático de las credenciales de conexión a través del archivo ace_info.json en tu GitHub.
"""
import json
import ssl
import sqlite3
import urllib.request
import urllib.parse
import urllib.error
from contextlib import closing


class ConectorNubeACE:
    def __init__(self, archivo_bd_local, url_info_github=""):
        self.archivo_bd = archivo_bd_local
        self.url_info_github = url_info_github
        self.supabase_url = ""
        self.supabase_key = ""
        self.activo = False
        self.ultimo_error = ""

    def configurar(self, supabase_url, supabase_key):
        self.supabase_url = (supabase_url or "").strip().rstrip("/")
        self.supabase_key = (supabase_key or "").strip()
        self.activo = bool(self.supabase_url.startswith("https://") and len(self.supabase_key) > 20)
        return self.activo

    def descubrir_desde_github(self, timeout=3.5):
        """Descarga la configuración del servidor en la nube desde tu página de GitHub (ace_info.json)."""
        if not self.url_info_github:
            return False, "Sin URL de GitHub configurada."
        try:
            ctx = ssl.create_default_context()
            req = urllib.request.Request(
                self.url_info_github,
                headers={"User-Agent": "ControlHorarioACE-CloudSync/20.9", "Cache-Control": "no-cache"}
            )
            with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
                datos = json.loads(resp.read(65536).decode("utf-8"))
            url_nube = datos.get("cloud_supabase_url", "")
            key_nube = datos.get("cloud_supabase_anon_key", "")
            if self.configurar(url_nube, key_nube):
                return True, f"Servidor en la nube configurado desde GitHub ({self.supabase_url})"
            return False, "El archivo ace_info.json de GitHub aún no contiene cloud_supabase_url."
        except Exception as e:
            return False, f"No se pudo leer ace_info.json desde GitHub: {e}"

    def _headers(self, extra=None):
        h = {
            "apikey": self.supabase_key,
            "Authorization": f"Bearer {self.supabase_key}",
            "Content-Type": "application/json",
            "Accept": "application/json",
        }
        if extra:
            h.update(extra)
        return h

    def _peticion(self, metodo, endpoint, payload=None, timeout=4.0, extra_headers=None):
        if not self.activo:
            raise RuntimeError("Conector de nube no configurado.")
        url = f"{self.supabase_url}{endpoint}"
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8") if payload is not None else None
        ctx = ssl.create_default_context()
        req = urllib.request.Request(url, data=data, method=metodo, headers=self._headers(extra_headers))
        with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
            raw = resp.read()
            return json.loads(raw.decode("utf-8")) if raw else None

    def sincronizar_empleados_descarga(self, empleados_db_actual):
        """Descarga la plantilla de empleados desde la nube para que Móvil y PC tengan las mismas claves y horarios."""
        if not self.activo:
            return empleados_db_actual, False
        try:
            filas = self._peticion("GET", "/rest/v1/empleados?select=*")
            if not isinstance(filas, list) or not filas:
                return empleados_db_actual, False
            nuevo = dict(empleados_db_actual)
            for r in filas:
                num = str(r.get("num_empleado", "")).strip()
                if not num:
                    continue
                nuevo[num] = {
                    "nombre": r.get("nombre", ""),
                    "departamento": r.get("departamento", ""),
                    "jornada": r.get("jornada", "Normal"),
                    "horario_manana": r.get("horario_manana", ""),
                    "horario_tarde": r.get("horario_tarde", ""),
                    "jornada_horas": r.get("jornada_horas", 8.0),
                    "clave": r.get("clave", ""),
                    "activo": bool(r.get("activo", True)),
                    "marcaje_auto": bool(r.get("marcaje_auto", True)),
                }
            return nuevo, True
        except Exception as e:
            self.ultimo_error = str(e)
            return empleados_db_actual, False

    def subir_empleado_a_nube(self, num, datos_emp):
        """Cuando el Admin crea o modifica un empleado en el PC o en el Móvil, lo actualiza en la nube al instante."""
        if not self.activo:
            return False
        try:
            payload = {
                "num_empleado": str(num),
                "nombre": datos_emp.get("nombre", ""),
                "departamento": datos_emp.get("departamento", ""),
                "jornada": datos_emp.get("jornada", "Normal"),
                "horario_manana": datos_emp.get("horario_manana", ""),
                "horario_tarde": datos_emp.get("horario_tarde", ""),
                "jornada_horas": datos_emp.get("jornada_horas", 8.0),
                "clave": datos_emp.get("clave", ""),
                "activo": bool(datos_emp.get("activo", True)),
                "marcaje_auto": bool(datos_emp.get("marcaje_auto", True)),
            }
            self._peticion(
                "POST",
                "/rest/v1/empleados",
                payload=payload,
                extra_headers={"Prefer": "resolution=merge-duplicates"}
            )
            return True
        except Exception as e:
            self.ultimo_error = str(e)
            return False

    def descargar_nuevos_eventos_a_sqlite(self):
        """
        Trae inmediatamente al SQLite local (del PC o del Móvil) todos los fichajes y correcciones nuevos
        que se hayan registrado desde otros dispositivos.
        Así, si el empleado fichó ENTRADA en el móvil, el PC ya la tiene antes de evaluar actualizar_botones().
        """
        if not self.activo:
            return False, "Modo local (Nube desactivada)"
        try:
            with closing(sqlite3.connect(self.archivo_bd, timeout=15)) as conn:
                row_r = conn.execute("SELECT COALESCE(MAX(id), 0) FROM registros").fetchone()
                max_id_r = int(row_r[0] or 0)
                row_c = conn.execute("SELECT COALESCE(MAX(id), 0) FROM correcciones").fetchone()
                max_id_c = int(row_c[0] or 0)

                nuevos_reg = self._peticion(
                    "GET",
                    f"/rest/v1/registros?id=gt.{max_id_r}&order=id.asc"
                ) or []
                nuevas_corr = self._peticion(
                    "GET",
                    f"/rest/v1/correcciones?id=gt.{max_id_c}&order=id.asc"
                ) or []

                for r in nuevos_reg:
                    conn.execute("""
                        INSERT OR IGNORE INTO registros (
                            id, fecha, hora, tipo_registro, num_empleado, nombre_apellidos,
                            departamento, tipo_jornada, horario, timestamp_sellado,
                            hash_evento, hash_anterior, timestamp_utc, desvio_reloj_s, hash_ver, origen
                        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                    """, (
                        r["id"], r["fecha"], r["hora"], r["tipo_registro"], r["num_empleado"],
                        r["nombre_apellidos"], r["departamento"], r["tipo_jornada"], r["horario"],
                        r["timestamp_sellado"], r["hash_evento"], r["hash_anterior"],
                        r.get("timestamp_utc", ""), r.get("desvio_reloj_s"), r.get("hash_ver", 2),
                        r.get("origen", "FICHAJE_NUBE")
                    ))

                for c in nuevas_corr:
                    conn.execute("""
                        INSERT OR IGNORE INTO correcciones (
                            id, timestamp_sellado, timestamp_utc, accion, registro_id, correccion_ref,
                            num_empleado, nombre_apellidos, fecha, hora, tipo_registro, motivo,
                            documento, conforme_trabajador, autor, hash_evento, hash_anterior
                        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                    """, (
                        c["id"], c["timestamp_sellado"], c["timestamp_utc"], c["accion"],
                        c.get("registro_id"), c.get("correccion_ref"), c["num_empleado"],
                        c["nombre_apellidos"], c.get("fecha", ""), c.get("hora", ""),
                        c.get("tipo_registro", ""), c["motivo"], c.get("documento", ""),
                        int(c.get("conforme_trabajador", 0)), c["autor"],
                        c["hash_evento"], c["hash_anterior"]
                    ))
                conn.commit()
            return True, f"Sincronizado (+{len(nuevos_reg)} fichajes, +{len(nuevas_corr)} correcciones)"
        except Exception as e:
            self.ultimo_error = str(e)
            return False, f"Sin conexión a nube ({e})"

    def registrar_fichaje_atomico_nube(self, fecha, hora, tipo, num, nom, dep, jor, hor, ts, utc, desvio, origen):
        """
        Envía el fichaje a la función RPC atómica de PostgreSQL para que el servidor encadene el hash
        sin riesgo de colisión si dos trabajadores fichan a la vez desde móvil y PC, y lo guarda en SQLite local.
        """
        res = self._peticion("POST", "/rest/v1/rpc/rpc_registrar_fichaje", payload={
            "p_fecha": fecha,
            "p_hora": hora,
            "p_tipo": tipo,
            "p_num": num,
            "p_nom": nom,
            "p_dep": dep,
            "p_jor": jor,
            "p_hor": hor,
            "p_ts": ts,
            "p_utc": utc,
            "p_desvio": desvio,
            "p_origen": origen,
        })
        # Inmediatamente sincroniza el registro recién creado hacia el SQLite local
        self.descargar_nuevos_eventos_a_sqlite()
        return {
            "id": res["id"],
            "fecha": fecha,
            "hora": hora,
            "ts": ts,
            "hash": res["hash_evento"],
            "jornada": jor,
            "desvio": desvio,
            "nombre": nom,
        }

    def subir_registro_existente(self, id_, fecha, hora, tipo, num, nom, dep, jor, hor,
                                 ts, hash_evento, hash_anterior, utc, desvio, hash_ver=2, origen="FICHAJE_PC"):
        """Replica un fichaje ya sellado en el PC hacia la tabla registros de Supabase."""
        if not self.activo:
            return False
        payload = {
            "id": int(id_),
            "fecha": fecha,
            "hora": hora,
            "tipo_registro": tipo,
            "num_empleado": num,
            "nombre_apellidos": nom,
            "departamento": dep,
            "tipo_jornada": jor,
            "horario": hor,
            "timestamp_sellado": ts,
            "hash_evento": hash_evento,
            "hash_anterior": hash_anterior,
            "timestamp_utc": utc,
            "desvio_reloj_s": desvio,
            "hash_ver": int(hash_ver),
            "origen": origen,
        }
        self._peticion(
            "POST",
            "/rest/v1/registros",
            payload=payload,
            extra_headers={"Prefer": "resolution=merge-duplicates"}
        )
        return True

    def migrar_todo_local_a_nube(self, empleados_dict):
        """
        Script de trasvase inicial: sube todos los empleados, registros históricos y correcciones
        del PC (registro_horario.db y empleados.json) a Supabase en un solo paso.
        """
        if not self.activo:
            raise RuntimeError("Conector de nube no activo. Configure URL y Anon Key primero.")
        n_emp = 0
        for num, d in (empleados_dict or {}).items():
            if self.subir_empleado_a_nube(num, d):
                n_emp += 1

        n_reg = 0
        n_corr = 0
        with closing(sqlite3.connect(self.archivo_bd, timeout=15)) as conn:
            filas_r = conn.execute(
                "SELECT id, fecha, hora, tipo_registro, num_empleado, nombre_apellidos, departamento, "
                "tipo_jornada, horario, timestamp_sellado, hash_evento, hash_anterior, timestamp_utc, "
                "desvio_reloj_s, hash_ver, origen FROM registros ORDER BY id ASC"
            ).fetchall()
            for r in filas_r:
                self.subir_registro_existente(*r)
                n_reg += 1

            filas_c = conn.execute(
                "SELECT id, timestamp_sellado, timestamp_utc, accion, registro_id, correccion_ref, "
                "num_empleado, nombre_apellidos, fecha, hora, tipo_registro, motivo, documento, "
                "conforme_trabajador, autor, hash_evento, hash_anterior FROM correcciones ORDER BY id ASC"
            ).fetchall()
            for c in filas_c:
                payload_c = {
                    "id": int(c[0]),
                    "timestamp_sellado": c[1],
                    "timestamp_utc": c[2],
                    "accion": c[3],
                    "registro_id": c[4],
                    "correccion_ref": c[5],
                    "num_empleado": c[6],
                    "nombre_apellidos": c[7],
                    "fecha": c[8] or "",
                    "hora": c[9] or "",
                    "tipo_registro": c[10] or "",
                    "motivo": c[11],
                    "documento": c[12] or "",
                    "conforme_trabajador": int(c[13] or 0),
                    "autor": c[14],
                    "hash_evento": c[15],
                    "hash_anterior": c[16],
                }
                self._peticion(
                    "POST",
                    "/rest/v1/correcciones",
                    payload=payload_c,
                    extra_headers={"Prefer": "resolution=merge-duplicates"}
                )
                n_corr += 1
        return {"empleados": n_emp, "registros": n_reg, "correcciones": n_corr}
