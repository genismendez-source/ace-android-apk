# -*- coding: utf-8 -*-
"""
CONTROL HORARIO LEGAL - ACE [VER.20.9rev6igem-CLOUD-MOBILE]
(c) SERVICIOS TECNOLOGICOS AI, SL 2026
Versión Android 10+ / iOS con Sincronización en Tiempo Real en la Nube (Opción B - Supabase + GitHub)
y Portal Completo de Consulta del Trabajador (Mis Registros + Resumen Mensual Art. 35.5 ET) y Administrador.
"""
import csv
import datetime
import os
import json
import threading
import time
import sqlite3
import hashlib
import hmac
import secrets
import socket
import struct
import re
import logging
import platform
import uuid
import base64
import ssl
import urllib.error
import urllib.request
from contextlib import closing

import flet as ft
from ace_cloud_sync import ConectorNubeACE

try:
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
    _CRYPTO_ED25519_OK = True
except ImportError:
    Ed25519PublicKey = None
    _CRYPTO_ED25519_OK = False


def _resolver_directorios_app():
    base_data = (
        os.environ.get("FLET_APP_STORAGE_DATA")
        or os.environ.get("ANDROID_PRIVATE")
        or os.path.join(os.path.expanduser("~"), ".control_horario_ace_mobile")
    )
    dir_datos = os.path.join(base_data, "datos")
    dir_seg = os.path.join(base_data, "seguridad_keystore")
    os.makedirs(dir_datos, exist_ok=True)
    os.makedirs(dir_seg, exist_ok=True)
    return dir_datos, dir_seg


BASE_DIR, DIR_SEGURIDAD = _resolver_directorios_app()

ARCHIVO_BD = os.path.join(BASE_DIR, "registro_horario.db")
ARCHIVO_EMPLEADOS = os.path.join(BASE_DIR, "empleados.json")
ARCHIVO_CONFIG = os.path.join(BASE_DIR, "config.json")
ARCHIVO_SEGURIDAD = os.path.join(BASE_DIR, "seguridad.json")
ARCHIVO_LOG = os.path.join(BASE_DIR, "control_horario.log")
ARCHIVO_CLAVE_HMAC = os.path.join(DIR_SEGURIDAD, "hmac.key.enc")
ARCHIVO_SECRETO_DISPOSITIVO = os.path.join(DIR_SEGURIDAD, ".device_keystore_master.bin")
ARCHIVO_HW_ANCHOR = os.path.join(DIR_SEGURIDAD, ".hw2_device_id.dat")
ARCHIVO_ANCLA = os.path.join(DIR_SEGURIDAD, "ancla_local.log")
CARPETA_EXPORT = os.path.join(BASE_DIR, "EXPORTACIONES_ITSS")
ARCHIVO_LICENCIA = os.path.join(DIR_SEGURIDAD, "licencia_activa.dat")

URL_REVOCACIONES = "https://raw.githubusercontent.com/genismendez-source/ace-licencias/main/ace_crl.json"
URL_INFO_GITHUB = "https://raw.githubusercontent.com/genismendez-source/ace-licencias/main/ace_info.json"
URL_LICENCIAS_BASE = "https://raw.githubusercontent.com/genismendez-source/ace-licencias/main/licencias/"

VERSION = "VER.20.9rev6igem-CLOUD"
CLAVE_PUBLICA_ED25519_HEX = "PENDIENTE_GENERAR_CON_GENERAR_LICENCIA_PY"
DIAS_PRUEBA_NUEVA = 5
DIAS_GRACIA_LICENCIA = 15
EMPLEADO_POR_DEFECTO = "001"
GENESIS = "GENESIS"
TIPOS_VALIDOS = ("ENTRADA", "INICIO PAUSA", "FIN PAUSA", "SALIDA")
TRANSICIONES = {
    "FUERA": ("ENTRADA",),
    "DENTRO": ("INICIO PAUSA", "SALIDA"),
    "PAUSA": ("FIN PAUSA",),
}
PBKDF2_ITER = 200_000
MAX_INTENTOS = 5
SEGUNDOS_BLOQUEO = 300
TOLERANCIA_SALTO_RELOJ_S = 60
AUTOR_AUTO = "SISTEMA (marcaje automático)"

CFG_DEFECTO = {
    "pausa_computa_como_trabajo": False,
    "tolerancia_reloj_s": 120,
    "max_horas_jornada_abierta": 16,
    "auto_marcaje_activo": True,
    "auto_marcaje_tolerancia_min": 15,
    "auto_marcaje_dias": [0, 1, 2, 3, 4],
    "festivos": {},
    "cloud_supabase_url": "",
    "cloud_supabase_anon_key": "",
}

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("ace_cloud_mobile")

empleados_db = {}
config = {}
_hmac_key = None
_REF_WALL = time.time()
_REF_MONO = time.monotonic()
ntp_cache = {"offset": None, "ts": 0.0, "servidor": ""}


class ErrorFichaje(Exception):
    pass


class ErrorSistema(Exception):
    pass


def escribir_json_atomico(ruta, datos):
    tmp = ruta + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(datos, f, indent=4, ensure_ascii=False)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, ruta)


def csv_seguro(valor):
    s = "" if valor is None else str(valor)
    if s and s[0] in ("=", "+", "-", "@", "	", "
"):
        return "'" + s
    return s


def escribir_csv(ruta, cabecera, filas):
    os.makedirs(os.path.dirname(ruta), exist_ok=True)
    with open(ruta, mode="w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(cabecera)
        for fila in filas:
            w.writerow([csv_seguro(c) for c in fila])


def fmt_hm(segundos):
    segundos = max(0, int(segundos))
    return f"{segundos // 3600}h {(segundos % 3600) // 60}m"


def ahora_local():
    return datetime.datetime.now().astimezone()


def a_utc_iso(dt_aware):
    return dt_aware.astimezone(datetime.timezone.utc).isoformat(timespec="milliseconds")


def parse_local(fecha, hora):
    return datetime.datetime.strptime(f"{fecha} {hora}", "%d/%m/%Y %H:%M:%S")


def naive_a_utc(dt_naive):
    return dt_naive.astimezone(datetime.timezone.utc)


def _parse_fecha_filtro(texto):
    texto = (texto or "").strip()
    if not texto:
        return None
    return datetime.datetime.strptime(texto, "%d/%m/%Y").date()


def cargar_configuracion():
    cfg = dict(CFG_DEFECTO)
    if os.path.exists(ARCHIVO_CONFIG):
        try:
            with open(ARCHIVO_CONFIG, "r", encoding="utf-8") as f:
                datos = json.load(f)
            if isinstance(datos, dict):
                cfg.update(datos)
        except Exception:
            pass
    return cfg


def guardar_configuracion():
    try:
        escribir_json_atomico(ARCHIVO_CONFIG, config)
    except Exception:
        pass


config = cargar_configuracion()
nube = ConectorNubeACE(ARCHIVO_BD, URL_INFO_GITHUB)
if config.get("cloud_supabase_url") and config.get("cloud_supabase_anon_key"):
    nube.configurar(config["cloud_supabase_url"], config["cloud_supabase_anon_key"])


def hash_clave(clave):
    sal = secrets.token_bytes(16)
    h = hashlib.pbkdf2_hmac("sha256", clave.encode("utf-8"), sal, PBKDF2_ITER)
    return f"pbkdf2${PBKDF2_ITER}${sal.hex()}${h.hex()}"


def es_hash_clave(valor):
    return isinstance(valor, str) and valor.startswith("pbkdf2$")


def verificar_clave(clave, almacenado):
    if not almacenado:
        return False
    if es_hash_clave(almacenado):
        try:
            _, it, sal, h = almacenado.split("$")
            calc = hashlib.pbkdf2_hmac("sha256", clave.encode("utf-8"), bytes.fromhex(sal), int(it))
            return hmac.compare_digest(calc.hex(), h)
        except Exception:
            return False
    return hmac.compare_digest(clave.encode("utf-8"), str(almacenado).encode("utf-8"))


_ARCHIVO_CLAVE_MAGIA = b"ACEK1_MOB
"


def _obtener_secreto_hardware_local():
    if os.path.exists(ARCHIVO_SECRETO_DISPOSITIVO):
        with open(ARCHIVO_SECRETO_DISPOSITIVO, "rb") as f:
            s = f.read()
        if len(s) == 32:
            return s
    s = secrets.token_bytes(32)
    with open(ARCHIVO_SECRETO_DISPOSITIVO, "wb") as f:
        f.write(s)
    return s


def obtener_clave_hmac():
    global _hmac_key
    if _hmac_key:
        return _hmac_key
    if os.path.exists(ARCHIVO_CLAVE_HMAC):
        with open(ARCHIVO_CLAVE_HMAC, "rb") as f:
            raw = f.read()
        if len(raw) >= 32:
            _hmac_key = raw[-32:]
            return _hmac_key
    nueva = secrets.token_bytes(32)
    with open(ARCHIVO_CLAVE_HMAC, "wb") as f:
        f.write(_ARCHIVO_CLAVE_MAGIA + nueva)
    _hmac_key = nueva
    return _hmac_key


def sellar(payload):
    return hmac.new(obtener_clave_hmac(), payload.encode("utf-8"), hashlib.sha256).hexdigest()


def payload_registro_v2(fecha, hora, tipo, num, nom, dep, jor, hor, ts, utc, desvio, hant):
    return json.dumps(
        ["v2", fecha, hora, tipo, num, nom, dep, jor, hor, ts, utc, desvio, hant],
        ensure_ascii=False, separators=(",", ":")
    )


# ==============================================================================
# BASE DE DATOS SQLITE LOCAL (CACHÉ ESPEJO + MODO OFFLINE + TRIGGERS)
# ==============================================================================
SQL_CREAR_REGISTROS = """
CREATE TABLE IF NOT EXISTS registros (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    fecha TEXT NOT NULL,
    hora TEXT NOT NULL,
    tipo_registro TEXT NOT NULL,
    num_empleado TEXT NOT NULL,
    nombre_apellidos TEXT NOT NULL,
    departamento TEXT NOT NULL,
    tipo_jornada TEXT NOT NULL,
    horario TEXT NOT NULL,
    timestamp_sellado TEXT NOT NULL,
    hash_evento TEXT NOT NULL,
    hash_anterior TEXT NOT NULL,
    timestamp_utc TEXT NOT NULL DEFAULT '',
    desvio_reloj_s REAL,
    hash_ver INTEGER NOT NULL DEFAULT 1,
    origen TEXT NOT NULL DEFAULT 'FICHAJE'
)
"""

SQL_CREAR_CORRECCIONES = """
CREATE TABLE IF NOT EXISTS correcciones (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    timestamp_sellado TEXT NOT NULL,
    timestamp_utc TEXT NOT NULL,
    accion TEXT NOT NULL,
    registro_id INTEGER,
    correccion_ref INTEGER,
    num_empleado TEXT NOT NULL,
    nombre_apellidos TEXT NOT NULL,
    fecha TEXT,
    hora TEXT,
    tipo_registro TEXT,
    motivo TEXT NOT NULL,
    documento TEXT NOT NULL DEFAULT '',
    conforme_trabajador INTEGER NOT NULL DEFAULT 0,
    autor TEXT NOT NULL,
    hash_evento TEXT NOT NULL,
    hash_anterior TEXT NOT NULL
)
"""

SQL_CREAR_BLOQUEOS = """
CREATE TABLE IF NOT EXISTS seguridad_bloqueos (
    clave_bloqueo TEXT PRIMARY KEY,
    intentos INTEGER NOT NULL DEFAULT 0,
    bloqueado_hasta REAL NOT NULL DEFAULT 0.0
)
"""

SQL_CREAR_AUDITORIA = """
CREATE TABLE IF NOT EXISTS auditoria_accesos (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    timestamp TEXT NOT NULL,
    usuario TEXT NOT NULL,
    accion TEXT NOT NULL,
    detalle TEXT NOT NULL
)
"""

SQL_TRIGGERS = """
CREATE TRIGGER IF NOT EXISTS trg_registros_no_update BEFORE UPDATE ON registros
BEGIN SELECT RAISE(ABORT, 'Registro inalterable: UPDATE bloqueado'); END;
CREATE TRIGGER IF NOT EXISTS trg_registros_no_delete BEFORE DELETE ON registros
BEGIN SELECT RAISE(ABORT, 'Registro inalterable: DELETE bloqueado'); END;
CREATE TRIGGER IF NOT EXISTS trg_correcciones_no_update BEFORE UPDATE ON correcciones
BEGIN SELECT RAISE(ABORT, 'Correccion inalterable: UPDATE bloqueado'); END;
CREATE TRIGGER IF NOT EXISTS trg_correcciones_no_delete BEFORE DELETE ON correcciones
BEGIN SELECT RAISE(ABORT, 'Correccion inalterable: DELETE bloqueado'); END;
"""


def abrir_bd():
    return sqlite3.connect(ARCHIVO_BD, timeout=15)


def inicializar_base_datos():
    with closing(abrir_bd()) as conn:
        conn.execute(SQL_CREAR_REGISTROS)
        conn.execute(SQL_CREAR_CORRECCIONES)
        conn.execute(SQL_CREAR_BLOQUEOS)
        conn.execute(SQL_CREAR_AUDITORIA)
        conn.executescript(SQL_TRIGGERS)
        conn.commit()


def cargar_empleados():
    global empleados_db
    if not os.path.exists(ARCHIVO_EMPLEADOS):
        empleados_db = {
            "001": {
                "nombre": "Empleado 001 (Demo)",
                "departamento": "General",
                "jornada": "Normal",
                "horario_manana": "08:00-14:00",
                "horario_tarde": "15:00-17:00",
                "jornada_horas": 8.0,
                "clave": hash_clave("1234"),
                "activo": True,
                "marcaje_auto": True,
            }
        }
        escribir_json_atomico(ARCHIVO_EMPLEADOS, empleados_db)
    else:
        try:
            with open(ARCHIVO_EMPLEADOS, "r", encoding="utf-8") as f:
                empleados_db = json.load(f)
        except Exception:
            empleados_db = {}

    if nube.activo:
        emp_remotos, ok = nube.sincronizar_empleados_descarga(empleados_db)
        if ok:
            empleados_db = emp_remotos
            escribir_json_atomico(ARCHIVO_EMPLEADOS, empleados_db)


def leer_seguridad():
    if os.path.exists(ARCHIVO_SEGURIDAD):
        try:
            with open(ARCHIVO_SEGURIDAD, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return {}


def comprobar_admin(clave):
    almacenado = leer_seguridad().get("admin", "")
    if not almacenado:
        # En la demo inicial, si aún no se creó clave de admin, acepta 'admin1234' y la guarda cifrada
        if clave == "admin1234":
            datos = leer_seguridad()
            datos["admin"] = hash_clave("admin1234")
            escribir_json_atomico(ARCHIVO_SEGURIDAD, datos)
            return "ok"
        return "mal"
    return "ok" if verificar_clave(clave, almacenado) else "mal"


def comprobar_clave_empleado(num, clave):
    emp = empleados_db.get(num)
    if not emp or not emp.get("clave"):
        return "sin_clave"
    if verificar_clave(clave, emp["clave"]):
        return "ok"
    return "mal"


# ==============================================================================
# HORA FIABLE Y CÁLCULO DE JORNADAS / RESUMEN MENSUAL (IDÉNTICO A PC)
# ==============================================================================
def consultar_hora_https_github(timeout=2.5):
    ctx = ssl.create_default_context()
    req = urllib.request.Request(URL_REVOCACIONES, method="HEAD", headers={"Cache-Control": "no-cache"})
    t1 = time.time()
    with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
        t4 = time.time()
        date_hdr = resp.headers.get("Date")
    dt_srv = datetime.datetime.strptime(date_hdr, "%a, %d %b %Y %H:%M:%S GMT").replace(tzinfo=datetime.timezone.utc)
    return dt_srv.timestamp() - (t1 + t4) / 2


def actualizar_ntp():
    try:
        offset = consultar_hora_https_github(2.5)
        ntp_cache.update({"offset": offset, "ts": time.time(), "servidor": "HTTPS Oficial"})
        return True
    except Exception:
        return False


def verificar_reloj():
    deriva = (time.time() - _REF_WALL) - (time.monotonic() - _REF_MONO)
    if abs(deriva) > TOLERANCIA_SALTO_RELOJ_S:
        return False, None, f"Detectado salto manual en el reloj del dispositivo ({deriva:+.0f}s)."
    offset = ntp_cache["offset"]
    if offset is not None and abs(offset) > float(config.get("tolerancia_reloj_s", 120)):
        return False, round(offset, 1), f"El reloj difiere {offset:+.0f}s de la hora oficial."
    return True, (round(offset, 1) if offset is not None else None), ""


def estado_tras(tipo):
    return {"ENTRADA": "DENTRO", "FIN PAUSA": "DENTRO", "INICIO PAUSA": "PAUSA", "SALIDA": "FUERA"}.get(tipo, "FUERA")


def cargar_eventos_efectivos(conn, num=None):
    filtro = " WHERE num_empleado = ?" if num else ""
    params = (num,) if num else ()
    originales = conn.execute(
        "SELECT id, fecha, hora, tipo_registro, num_empleado, nombre_apellidos, departamento, tipo_jornada, "
        "horario, timestamp_utc, origen FROM registros" + filtro + " ORDER BY id ASC", params).fetchall()
    correcciones = conn.execute(
        "SELECT id, accion, registro_id, correccion_ref, num_empleado, nombre_apellidos, fecha, hora, "
        "tipo_registro, conforme_trabajador, autor FROM correcciones" + filtro + " ORDER BY id ASC", params).fetchall()

    anulados = set()
    corr_anuladas = set()
    for c in correcciones:
        _, accion, registro_id, correccion_ref = c[0], c[1], c[2], c[3]
        if accion in ("ANULAR", "MODIFICAR") and registro_id:
            anulados.add(registro_id)
        if accion == "ANULAR" and correccion_ref:
            corr_anuladas.add(correccion_ref)

    ultima_mod = {}
    for c in correcciones:
        if c[1] == "MODIFICAR" and c[2] and c[0] not in corr_anuladas:
            ultima_mod[c[2]] = c[0]

    eventos = []
    info_corr = set()
    ultimos = {}
    for (id_, fecha, hora, tipo, n, nom, dep, jor, hor, utc, origen) in originales:
        ultimos[n] = (nom, dep, jor, hor)
        try:
            dt = parse_local(fecha, hora)
        except ValueError:
            continue
        if id_ in anulados:
            info_corr.add((n, fecha))
            continue
        try:
            ts = datetime.datetime.fromisoformat(utc) if utc else naive_a_utc(dt)
        except ValueError:
            ts = naive_a_utc(dt)
        eventos.append({"id": id_, "orden": (0, id_), "dt": dt, "ts": ts, "tipo": tipo, "num": n, "nombre": nom,
                        "dep": dep, "jornada": jor, "horario": hor, "corr": False, "conforme": True,
                        "auto": False, "origen": origen})

    for (cid, accion, registro_id, correccion_ref, n, nom, fecha, hora, tipo, conforme, autor_corr) in correcciones:
        if accion not in ("ALTA", "MODIFICAR") or cid in corr_anuladas:
            continue
        if accion == "MODIFICAR" and ultima_mod.get(registro_id) != cid:
            continue
        try:
            dt = parse_local(fecha, hora)
        except (ValueError, TypeError):
            continue
        nom_h, dep, jor, hor = ultimos.get(n, (nom, "", "Normal", ""))
        eventos.append({"id": f"C{cid}", "orden": (1, cid), "dt": dt, "ts": naive_a_utc(dt), "tipo": tipo, "num": n,
                        "nombre": nom or nom_h, "dep": dep, "jornada": jor, "horario": hor, "corr": True,
                        "conforme": bool(conforme), "auto": autor_corr == AUTOR_AUTO, "origen": "CORRECCION"})
    eventos.sort(key=lambda e: (e["ts"], e["orden"]))
    return eventos, info_corr


def agrupar_jornadas(eventos_emp, max_horas):
    grupos = []
    por_fecha = {}
    estado = "FUERA"
    clave = None
    prev_ts = None
    for ev in eventos_emp:
        if estado != "FUERA" and prev_ts is not None and (ev["ts"] - prev_ts).total_seconds() > max_horas * 3600:
            por_fecha[clave]["anom"].add("Jornada sin cerrar")
            estado = "FUERA"
        d = ev["dt"].date()
        if estado == "FUERA":
            clave = d
            if clave not in por_fecha:
                g = {"fecha": clave, "eventos": [], "anom": set()}
                por_fecha[clave] = g
                grupos.append(g)
        g = por_fecha[clave]
        g["eventos"].append(ev)
        if ev["tipo"] in TRANSICIONES.get(estado, ()):
            estado = estado_tras(ev["tipo"])
        else:
            g["anom"].add("Secuencia anómala")
        prev_ts = ev["ts"]
    grupos.sort(key=lambda g: g["fecha"])
    return grupos


def calcular_trabajo(evs, ahora, pausa_computa, max_horas):
    work_start = None
    pause_start = None
    trabajo = 0.0
    pausa = 0.0
    estado = "FUERA"
    for ev in evs:
        t, ts = ev["tipo"], ev["ts"]
        if t == "ENTRADA" and estado == "FUERA":
            work_start, estado = ts, "DENTRO"
        elif t == "INICIO PAUSA" and estado == "DENTRO":
            trabajo += (ts - work_start).total_seconds()
            work_start, pause_start, estado = None, ts, "PAUSA"
        elif t == "FIN PAUSA" and estado == "PAUSA":
            pausa += (ts - pause_start).total_seconds()
            pause_start, work_start, estado = None, ts, "DENTRO"
        elif t == "SALIDA":
            if estado == "DENTRO":
                trabajo += (ts - work_start).total_seconds()
                work_start, estado = None, "FUERA"
            elif estado == "PAUSA":
                pausa += (ts - pause_start).total_seconds()
                pause_start, estado = None, "FUERA"
    abierta = estado != "FUERA"
    en_curso = False
    if abierta and evs:
        if (ahora - evs[-1]["ts"]).total_seconds() <= max_horas * 3600:
            en_curso = True
            if estado == "DENTRO":
                trabajo += (ahora - work_start).total_seconds()
            else:
                pausa += (ahora - pause_start).total_seconds()
    if pausa_computa:
        trabajo += pausa
    return {"trabajo_s": max(0.0, trabajo), "pausa_s": max(0.0, pausa), "abierta": abierta, "en_curso": en_curso}


def estado_empleado(conn, num, ahora=None):
    ahora = ahora or ahora_local()
    eventos, _ = cargar_eventos_efectivos(conn, num)
    if not eventos:
        return "FUERA", None
    ultimo = eventos[-1]
    estado = estado_tras(ultimo["tipo"])
    if estado != "FUERA":
        horas = (ahora - ultimo["ts"]).total_seconds() / 3600
        if horas > float(config.get("max_horas_jornada_abierta", 16)):
            return "CADUCADA", ultimo
    return estado, ultimo


def pausa_completada_en_jornada_actual(conn, num, ahora=None):
    ahora = ahora or ahora_local()
    eventos, _ = cargar_eventos_efectivos(conn, num)
    if not eventos:
        return False
    max_h = float(config.get("max_horas_jornada_abierta", 16))
    grupos = agrupar_jornadas(eventos, max_h)
    if not grupos:
        return False
    actual = grupos[-1]["eventos"]
    if not actual or estado_tras(actual[-1]["tipo"]) == "FUERA":
        return False
    if (ahora - actual[-1]["ts"]).total_seconds() > max_h * 3600:
        return False
    return any(e["tipo"] == "INICIO PAUSA" for e in actual) and any(e["tipo"] == "FIN PAUSA" for e in actual)


def construir_filas(conn, desde=None, hasta=None, num_filtro=None, ahora=None):
    ahora = ahora or ahora_local()
    max_h = float(config.get("max_horas_jornada_abierta", 16))
    pausa_computa = bool(config.get("pausa_computa_como_trabajo", False))
    eventos, info_corr = cargar_eventos_efectivos(conn, num_filtro)
    por_emp = {}
    for ev in eventos:
        if ev["num"]:
            por_emp.setdefault(ev["num"], []).append(ev)

    filas = []
    for num, evs in por_emp.items():
        horas_ref = empleados_db.get(num, {}).get("jornada_horas")
        for g in agrupar_jornadas(evs, max_h):
            clave = g["fecha"]
            if desde and clave < desde:
                continue
            if hasta and clave > hasta:
                continue
            calc = calcular_trabajo(g["eventos"], ahora, pausa_computa, max_h)
            ent = [e for e in g["eventos"] if e["tipo"] == "ENTRADA"]
            sal = [e for e in g["eventos"] if e["tipo"] == "SALIDA"]
            ipa = [e for e in g["eventos"] if e["tipo"] == "INICIO PAUSA"]
            fpa = [e for e in g["eventos"] if e["tipo"] == "FIN PAUSA"]

            incid = set(g["anom"])
            if calc["abierta"] and not calc["en_curso"]:
                incid.add("Jornada sin cerrar")
            if any(e["corr"] and not e["auto"] for e in g["eventos"]) or (num, clave.strftime("%d/%m/%Y")) in info_corr:
                incid.add("Corregido")
            if any(e["auto"] for e in g["eventos"]):
                incid.add("Marcaje automático")

            extra = None
            if isinstance(horas_ref, (int, float)) and horas_ref > 0:
                extra = max(0.0, calc["trabajo_s"] - horas_ref * 3600)

            primero = g["eventos"][0]
            origenes = sorted({e.get("origen", "FICHAJE") for e in g["eventos"]})
            filas.append({
                "date": clave,
                "fecha": clave.strftime("%d/%m/%Y"),
                "num": num,
                "nombre": primero["nombre"],
                "dep": primero["dep"],
                "jornada": primero["jornada"],
                "ent_m": ent[0]["dt"].strftime("%H:%M") if ent else "--:--",
                "sal_m": ("Trabajando..." if calc["en_curso"] and len(ent) == 1 and not sal else (sal[0]["dt"].strftime("%H:%M") if sal else "--:--")),
                "ini_p": ipa[0]["dt"].strftime("%H:%M") if ipa else "--:--",
                "fin_p": fpa[0]["dt"].strftime("%H:%M") if fpa else "--:--",
                "ent_t": ent[1]["dt"].strftime("%H:%M") if len(ent) > 1 else "--:--",
                "sal_t": ("Trabajando..." if calc["en_curso"] and len(ent) >= 2 and len(sal) == 1 else (sal[1]["dt"].strftime("%H:%M") if len(sal) > 1 else "--:--")),
                "trabajo_s": calc["trabajo_s"],
                "extra_s": extra,
                "incid": ", ".join(sorted(incid)),
                "origenes": " / ".join(origenes),
                "en_curso": calc["en_curso"],
            })
    filas.sort(key=lambda f: (f["date"], f["num"]), reverse=True)
    return filas


def resumen_mensual(filas):
    res = {}
    for f in filas:
        k = (f["num"], f["date"].strftime("%Y-%m"))
        r = res.setdefault(k, {
            "num": f["num"], "nombre": f["nombre"], "mes": k[1],
            "dias": 0, "trabajo_s": 0.0, "extra_s": 0.0,
            "extra_definido": True, "incidencias": 0
        })
        r["dias"] += 1
        r["trabajo_s"] += f["trabajo_s"]
        if f["extra_s"] is None:
            r["extra_definido"] = False
        else:
            r["extra_s"] += f["extra_s"]
        if f["incid"]:
            r["incidencias"] += 1
    return sorted(res.values(), key=lambda r: (r["mes"], r["num"]), reverse=True)


def registrar_evento(num, tipo, origen_dispositivo="FICHAJE_MOVIL"):
    """
    1. Sincroniza antes con la nube (para saber si el empleado fichó ENTRADA en el PC o en otro móvil).
    2. Valida transición legal (FUERA -> ENTRADA -> DENTRO -> SALIDA).
    3. Si la nube está activa, sella atómicamente en PostgreSQL (evitando colisiones de hash) y actualiza SQLite.
    """
    if nube.activo:
        nube.descargar_nuevos_eventos_a_sqlite()

    if tipo not in TIPOS_VALIDOS:
        raise ErrorFichaje("Tipo de registro no válido.")
    emp = empleados_db.get(num)
    if not emp:
        raise ErrorFichaje("El Nº de empleado no existe.")
    if not emp.get("activo", True):
        raise ErrorFichaje("El empleado está dado de baja.")

    ok, desvio, msg = verificar_reloj()
    if not ok:
        raise ErrorFichaje(msg)

    nom = emp.get("nombre", "")
    dep = emp.get("departamento", "")
    jor = emp.get("jornada", "Normal")
    horarios = []
    if emp.get("horario_manana"):
        horarios.append(f"M: {emp['horario_manana']}")
    if emp.get("horario_tarde"):
        horarios.append(f"T: {emp['horario_tarde']}")
    horario_completo = " | ".join(horarios) if horarios else "Sin horario"

    ahora = ahora_local()
    fecha = ahora.strftime("%d/%m/%Y")
    hora = ahora.strftime("%H:%M:%S")
    ts = ahora.isoformat(timespec="milliseconds")
    utc = a_utc_iso(ahora)

    with closing(abrir_bd()) as conn:
        estado, _ = estado_empleado(conn, num, ahora)
        if estado == "CADUCADA":
            raise ErrorFichaje("Su última jornada quedó SIN CERRAR. El administrador debe regularizarla.")
        if tipo not in TRANSICIONES[estado]:
            raise ErrorFichaje(f"Operación no permitida: está en estado {estado} y no puede fichar {tipo}.")
        if tipo == "INICIO PAUSA" and pausa_completada_en_jornada_actual(conn, num, ahora):
            raise ErrorFichaje("Ya ha completado la pausa única de esta jornada.")

    # Si está conectado a la nube (Opción B), registra en el servidor central para que el PC lo vea al instante
    if nube.activo:
        return nube.registrar_fichaje_atomico_nube(
            fecha, hora, tipo, num, nom, dep, jor, horario_completo, ts, utc, desvio, origen_dispositivo
        )

    # Modo local si no se ha configurado aún la URL de Supabase
    conn = abrir_bd()
    conn.isolation_level = None
    try:
        conn.execute("BEGIN IMMEDIATE")
        fila_h = conn.execute("SELECT hash_evento FROM registros ORDER BY id DESC LIMIT 1").fetchone()
        hash_anterior = fila_h[0] if fila_h else GENESIS
        payload = payload_registro_v2(fecha, hora, tipo, num, nom, dep, jor, horario_completo, ts, utc,
                                      desvio, hash_anterior)
        hash_evento = sellar(payload)
        cur = conn.execute("""
            INSERT INTO registros (fecha, hora, tipo_registro, num_empleado, nombre_apellidos, departamento,
                tipo_jornada, horario, timestamp_sellado, hash_evento, hash_anterior, timestamp_utc,
                desvio_reloj_s, hash_ver, origen)
            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, (fecha, hora, tipo, num, nom, dep, jor, horario_completo, ts, hash_evento, hash_anterior,
              utc, desvio, 2, origen_dispositivo))
        nuevo_id = cur.lastrowid
        conn.execute("COMMIT")
    except BaseException:
        if conn.in_transaction:
            conn.execute("ROLLBACK")
        raise
    finally:
        conn.close()

    return {"id": nuevo_id, "fecha": fecha, "hora": hora, "ts": ts, "hash": hash_evento, "jornada": jor,
            "desvio": desvio, "nombre": nom}


def codigo_solicitud_equipo():
    if os.path.exists(ARCHIVO_HW_ANCHOR):
        try:
            with open(ARCHIVO_HW_ANCHOR, "r", encoding="utf-8") as f:
                c = f.read().strip()
            if len(c) == 27:
                return c
        except Exception:
            pass
    nodo = str(uuid.getnode())
    so_info = f"{platform.system()}:{platform.machine()}"
    sem = _obtener_secreto_hardware_local().hex()
    s1 = hashlib.sha256(f"ACE_UUID:{nodo}:{sem[:12]}".encode()).hexdigest()[:6].upper()
    s2 = hashlib.sha256(f"ACE_GUID:{BASE_DIR}".encode()).hexdigest()[:6].upper()
    s3 = hashlib.sha256(f"ACE_SOC:{so_info}".encode()).hexdigest()[:6].upper()
    s4 = hashlib.sha256(f"ACE_VOL:{sem[12:24]}".encode()).hexdigest()[:6].upper()
    cod = f"{s1}-{s2}-{s3}-{s4}"
    try:
        with open(ARCHIVO_HW_ANCHOR, "w", encoding="utf-8") as f:
            f.write(cod)
    except Exception:
        pass
    return cod


def exportar_csv_itss(desde=None, hasta=None, num_filtro=None):
    if nube.activo:
        nube.descargar_nuevos_eventos_a_sqlite()
    sello = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    sufijo = f"_{num_filtro}" if num_filtro else "_TODOS"
    ruta_ev = os.path.join(CARPETA_EXPORT, f"Eventos_Sellados_ACE{sufijo}_{sello}.csv")
    ruta_res = os.path.join(CARPETA_EXPORT, f"Resumen_Mensual_ACE{sufijo}_{sello}.csv")
    with closing(abrir_bd()) as conn:
        filas = construir_filas(conn, desde=desde, hasta=hasta, num_filtro=num_filtro)
        res_m = resumen_mensual(filas)
        filtro_sql = " WHERE num_empleado = ?" if num_filtro else ""
        params = (num_filtro,) if num_filtro else ()
        crudos = conn.execute(
            "SELECT id, fecha, hora, tipo_registro, num_empleado, nombre_apellidos, departamento, tipo_jornada, "
            "horario, timestamp_sellado, timestamp_utc, desvio_reloj_s, hash_ver, origen, hash_anterior, hash_evento "
            "FROM registros" + filtro_sql + " ORDER BY id ASC", params
        ).fetchall()
    escribir_csv(
        ruta_ev,
        ("ID", "Fecha", "Hora", "Tipo", "Nº", "Nombre", "Departamento", "Jornada", "Horario",
         "Sellado", "UTC", "Desvío (s)", "Ver", "Origen (Móvil/PC)", "Hash Anterior", "Hash Evento"),
        crudos
    )
    escribir_csv(
        ruta_res,
        ("Mes", "Nº", "Nombre y Apellidos", "Días trabajados", "Total horas", "Horas extra", "Días con incidencias"),
        [(r["mes"], r["num"], r["nombre"], r["dias"], fmt_hm(r["trabajo_s"]),
          fmt_hm(r["extra_s"]) if r["extra_definido"] else "—", r["incidencias"]) for r in res_m]
    )
    return ruta_ev, ruta_res, len(crudos), len(res_m)


# ==============================================================================
# INTERFAZ MÓVIL COMPLETA:
#   1. Fichar (Sincronizado con PC en tiempo real)
#   2. Mis Consultas / Admin (Filtro Fechas + Detalle Diario + Resumen Mensual Art. 35.5 ET)
#   3. Nube (Opción B Supabase) + GitHub
# ==============================================================================
def main(page: ft.Page):
    page.title = f"Control Horario ACE [{VERSION}]"
    page.theme_mode = ft.ThemeMode.LIGHT
    page.padding = 0
    page.window_width = 440
    page.window_height = 860
    page.bgcolor = "#F4F6F9"

    inicializar_base_datos()
    obtener_clave_hmac()
    cargar_empleados()
    threading.Thread(target=actualizar_ntp, daemon=True).start()

    sesion_consulta = {
        "modo": None,          # "EMPLEADO" o "ADMIN"
        "num_autenticado": "", # Nº del empleado que abrió "Mis Registros"
        "vista_sub": "DIARIO", # "DIARIO" o "MENSUAL"
    }

    def notificar(texto, color="#1976D2"):
        page.snack_bar = ft.SnackBar(content=ft.Text(texto, color="white", weight=ft.FontWeight.BOLD), bgcolor=color)
        page.snack_bar.open = True
        page.update()

    # --------------------------------------------------------------------------
    # PESTAÑA 1: FICHAJE SINCRONIZADO MÓVIL <-> PC
    # --------------------------------------------------------------------------
    lbl_reloj = ft.Text(
        datetime.datetime.now().strftime("%d/%m/%Y  •  %H:%M:%S"),
        size=16, weight=ft.FontWeight.BOLD, color="#0F172A"
    )
    lbl_cloud_badge = ft.Text("", size=11, color="#93C5FD", weight=ft.FontWeight.BOLD)

    tf_num = ft.TextField(
        label="Nº Empleado", value=EMPLEADO_POR_DEFECTO,
        text_align=ft.TextAlign.CENTER, width=145, text_size=16, bgcolor="white", border_radius=8
    )
    tf_clave = ft.TextField(
        label="Clave Usuario", password=True, can_reveal_password=True,
        width=205, text_size=16, bgcolor="white", border_radius=8
    )

    lbl_estado_actual = ft.Text("Estado: Consultando...", size=14, weight=ft.FontWeight.BOLD, color="#1E40AF")
    lbl_ultimo_origen = ft.Text("", size=11, color="#475569", text_align=ft.TextAlign.CENTER)

    btn_entrada = ft.ElevatedButton(
        "FICHAR ENTRADA", icon=ft.icons.LOGIN, bgcolor="#2E7D32", color="white",
        height=48, expand=True, on_click=lambda _: ejecutar_fichaje("ENTRADA")
    )
    btn_ini_pausa = ft.ElevatedButton(
        "INICIO PAUSA", icon=ft.icons.FREE_BREAKFAST, bgcolor="#EF6C00", color="white",
        height=48, expand=True, on_click=lambda _: ejecutar_fichaje("INICIO PAUSA")
    )
    btn_fin_pausa = ft.ElevatedButton(
        "FIN PAUSA", icon=ft.icons.PLAY_ARROW, bgcolor="#1976D2", color="white",
        height=48, expand=True, on_click=lambda _: ejecutar_fichaje("FIN PAUSA")
    )
    btn_salida = ft.ElevatedButton(
        "FICHAR SALIDA", icon=ft.icons.LOGOUT, bgcolor="#C62828", color="white",
        height=48, expand=True, on_click=lambda _: ejecutar_fichaje("SALIDA")
    )

    def refrescar_estado_fichaje(_=None):
        if nube.activo:
            ok_s, msg_s = nube.descargar_nuevos_eventos_a_sqlite()
            lbl_cloud_badge.value = f"☁️ Nube Activa (PC ↔ Móvil en tiempo real)" if ok_s else f"⚠️ Nube sin red ({msg_s})"
        else:
            lbl_cloud_badge.value = "📱 Modo Local (Configure Supabase en pestaña Nube para sincronizar con PC)"

        num = (tf_num.value or "").strip()
        emp = empleados_db.get(num)
        if not emp:
            lbl_estado_actual.value = "Empleado no registrado"
            lbl_estado_actual.color = "#C62828"
            lbl_ultimo_origen.value = ""
            for b in (btn_entrada, btn_ini_pausa, btn_fin_pausa, btn_salida):
                b.disabled = True
            page.update()
            return

        with closing(abrir_bd()) as conn:
            est, ult = estado_empleado(conn, num)
            pausa_hecha = pausa_completada_en_jornada_actual(conn, num) if est == "DENTRO" else False

        if ult:
            lbl_ultimo_origen.value = (
                f"Último marcaje: {ult['tipo']} a las {ult['dt']:%H:%M:%S} del {ult['dt']:%d/%m/%Y} "
                f"[{ult.get('origen', 'FICHAJE')}]"
            )
        else:
            lbl_ultimo_origen.value = "Sin fichajes previos registrados"

        if est == "FUERA":
            lbl_estado_actual.value = "Estado: FUERA DE JORNADA"
            lbl_estado_actual.color = "#475569"
            btn_entrada.disabled = False
            btn_ini_pausa.disabled = True
            btn_fin_pausa.disabled = True
            btn_salida.disabled = True
        elif est == "DENTRO":
            lbl_estado_actual.value = (
                "Estado: TRABAJANDO (pausa completada)" if pausa_hecha else "Estado: TRABAJANDO (Puede fichar Salida aquí o en PC)"
            )
            lbl_estado_actual.color = "#2E7D32"
            btn_entrada.disabled = True
            btn_ini_pausa.disabled = pausa_hecha
            btn_fin_pausa.disabled = True
            btn_salida.disabled = False
        elif est == "PAUSA":
            lbl_estado_actual.value = "Estado: EN PAUSA"
            lbl_estado_actual.color = "#EF6C00"
            btn_entrada.disabled = True
            btn_ini_pausa.disabled = True
            btn_fin_pausa.disabled = False
            btn_salida.disabled = True
        else:
            lbl_estado_actual.value = "Jornada anterior SIN CERRAR (requiere corrección Admin)"
            lbl_estado_actual.color = "#C62828"
            for b in (btn_entrada, btn_ini_pausa, btn_fin_pausa, btn_salida):
                b.disabled = True
        page.update()

    tf_num.on_change = lambda _: (setattr(tf_clave, "value", ""), refrescar_estado_fichaje())

    def ejecutar_fichaje(tipo):
        num = (tf_num.value or "").strip()
        clave = (tf_clave.value or "").strip()
        if not clave:
            notificar("Introduzca su clave de usuario para fichar.", "#EF6C00")
            return
        if comprobar_clave_empleado(num, clave) != "ok":
            notificar("Clave de empleado incorrecta.", "#C62828")
            tf_clave.value = ""
            page.update()
            return
        try:
            info = registrar_evento(num, tipo, origen_dispositivo="FICHAJE_MOVIL")
        except Exception as e:
            notificar(str(e), "#C62828")
            refrescar_estado_fichaje()
            return

        tf_clave.value = ""
        refrescar_estado_fichaje()
        dlg = ft.AlertDialog(
            title=ft.Text(f"✅ {tipo} Sellada y Sincronizada", weight=ft.FontWeight.BOLD),
            content=ft.Text(
                f"Empleado: {info['nombre']} ({num})
"
                f"Registro Nº: {info['id']}
"
                f"Hora: {info['hora']} ({info['fecha']})
"
                f"Origen: FICHAJE_MOVIL
"
                f"Sello HMAC: {info['hash'][:20]}...

"
                f"Ya puede continuar o cerrar su jornada indistintamente desde este móvil o desde el PC."
            ),
            actions=[ft.TextButton("Aceptar", on_click=lambda _: page.close(dlg))],
        )
        page.open(dlg)

    def ir_directo_a_mis_registros(_):
        """Permite al empleado pasar directamente a consultar sus registros y resumen mensual validando su clave."""
        num = (tf_num.value or "").strip()
        clave = (tf_clave.value or "").strip()
        if comprobar_clave_empleado(num, clave) != "ok":
            notificar("Escriba su Nº de empleado y su clave para abrir Mis Registros.", "#EF6C00")
            return
        tf_clave.value = ""
        sesion_consulta["modo"] = "EMPLEADO"
        sesion_consulta["num_autenticado"] = num
        page.navigation_bar.selected_index = 1
        cambiar_pestana_manual(1)
        refrescar_panel_consultas()

    # --------------------------------------------------------------------------
    # PESTAÑA 2: PORTAL DE CONSULTAS EN EL MÓVIL (EMPLEADO Y ADMINISTRADOR)
    # --------------------------------------------------------------------------
    tf_login_cons_num = ft.TextField(label="Nº Empleado", value=EMPLEADO_POR_DEFECTO, width=120, bgcolor="white")
    tf_login_cons_pwd = ft.TextField(label="Clave Empleado o Admin", password=True, can_reveal_password=True, width=210, bgcolor="white")

    tf_filtro_desde = ft.TextField(label="Desde (DD/MM/AAAA)", width=155, text_size=12, bgcolor="white")
    tf_filtro_hasta = ft.TextField(label="Hasta (DD/MM/AAAA)", width=155, text_size=12, bgcolor="white")
    dd_filtro_emp = ft.Dropdown(label="Empleado", width=220, bgcolor="white")

    lbl_cabecera_consulta = ft.Text("Autentíquese para consultar sus registros o entre como Administrador", size=13, weight=ft.FontWeight.BOLD)
    lbl_totales_periodo = ft.Text("", size=12, weight=ft.FontWeight.BOLD, color="#1E40AF")

    contenedor_resultados_consulta = ft.Column(spacing=8, scroll=ft.ScrollMode.AUTO, expand=True)
    panel_controles_consulta = ft.Column(visible=False, spacing=8, expand=True)

    def login_consulta_empleado(_):
        num = (tf_login_cons_num.value or "").strip()
        pwd = (tf_login_cons_pwd.value or "").strip()
        if comprobar_clave_empleado(num, pwd) != "ok":
            notificar("Clave de trabajador incorrecta.", "#C62828")
            return
        tf_login_cons_pwd.value = ""
        sesion_consulta["modo"] = "EMPLEADO"
        sesion_consulta["num_autenticado"] = num
        refrescar_panel_consultas()

    def login_consulta_admin(_):
        pwd = (tf_login_cons_pwd.value or "").strip()
        if comprobar_admin(pwd) != "ok":
            notificar("Contraseña de Administrador incorrecta (Demo inicial: admin1234).", "#C62828")
            return
        tf_login_cons_pwd.value = ""
        sesion_consulta["modo"] = "ADMIN"
        sesion_consulta["num_autenticado"] = "TODOS"
        refrescar_panel_consultas()

    def cerrar_sesion_consulta(_):
        sesion_consulta["modo"] = None
        sesion_consulta["num_autenticado"] = ""
        panel_controles_consulta.visible = False
        lbl_cabecera_consulta.value = "Sesión de consulta cerrada. Introduzca su clave para consultar."
        page.update()

    def alternar_subvista_consulta(tipo_vista):
        sesion_consulta["vista_sub"] = tipo_vista
        refrescar_panel_consultas()

    def refrescar_panel_consultas(_=None):
        if not sesion_consulta["modo"]:
            panel_controles_consulta.visible = False
            page.update()
            return

        if nube.activo:
            nube.descargar_nuevos_eventos_a_sqlite()
            cargar_empleados()

        panel_controles_consulta.visible = True
        contenedor_resultados_consulta.controls.clear()

        if sesion_consulta["modo"] == "EMPLEADO":
            num_fijo = sesion_consulta["num_autenticado"]
            nom_emp = empleados_db.get(num_fijo, {}).get("nombre", num_fijo)
            lbl_cabecera_consulta.value = f"👤 Mis Registros: [{num_fijo}] {nom_emp}"
            dd_filtro_emp.options = [ft.dropdown.Option(num_fijo, f"{num_fijo} - {nom_emp}")]
            dd_filtro_emp.value = num_fijo
            dd_filtro_emp.disabled = True
        else:
            lbl_cabecera_consulta.value = "🛡️ Panel Administrador (Todos los Empleados — Móvil + PC)"
            opts = [ft.dropdown.Option("TODOS", "TODOS LOS EMPLEADOS")]
            for k, v in sorted(empleados_db.items()):
                opts.append(ft.dropdown.Option(k, f"{k} - {v.get('nombre', '')}"))
            dd_filtro_emp.options = opts
            if not dd_filtro_emp.value:
                dd_filtro_emp.value = "TODOS"
            dd_filtro_emp.disabled = False

        try:
            d_dt = _parse_fecha_filtro(tf_filtro_desde.value)
            h_dt = _parse_fecha_filtro(tf_filtro_hasta.value)
        except ValueError:
            notificar("Formato de fecha no válido. Use DD/MM/AAAA.", "#EF6C00")
            return

        num_query = (
            sesion_consulta["num_autenticado"]
            if sesion_consulta["modo"] == "EMPLEADO"
            else (None if dd_filtro_emp.value in (None, "TODOS") else dd_filtro_emp.value)
        )

        with closing(abrir_bd()) as conn:
            filas = construir_filas(conn, desde=d_dt, hasta=h_dt, num_filtro=num_query)

        total_seg = sum(f["trabajo_s"] for f in filas)
        total_ext = sum((f["extra_s"] or 0.0) for f in filas)
        lbl_totales_periodo.value = (
            f"Jornadas en filtro: {len(filas)}  |  Total Trabajado: {fmt_hm(total_seg)}  |  Horas Extra: {fmt_hm(total_ext)}"
        )

        if sesion_consulta["vista_sub"] == "DIARIO":
            if not filas:
                contenedor_resultados_consulta.controls.append(
                    ft.Text("No hay registros en el intervalo seleccionado.", color="#64748B")
                )
            for f in filas:
                extra_txt = fmt_hm(f["extra_s"]) if f["extra_s"] is not None else "—"
                incid_txt = f["incid"] or "Correcto"
                borde_col = "#16A34A" if f["en_curso"] else ("#EF6C00" if f["incid"] else "#CBD5E1")
                contenedor_resultados_consulta.controls.append(
                    ft.Container(
                        bgcolor="white",
                        padding=10,
                        border_radius=8,
                        border=ft.border.all(1.5, borde_col),
                        content=ft.Column([
                            ft.Row([
                                ft.Text(f"📅 {f['fecha']} — [{f['num']}] {f['nombre']}", weight=ft.FontWeight.BOLD, size=13),
                                ft.Text(f"⏱ {fmt_hm(f['trabajo_s'])}", weight=ft.FontWeight.BOLD, color="#1E40AF"),
                            ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
                            ft.Text(
                                f"Mañana: {f['ent_m']} a {f['sal_m']}  |  Pausa: {f['ini_p']}-{f['fin_p']}  |  Tarde: {f['ent_t']} a {f['sal_t']}",
                                size=11.5, color="#1E293B"
                            ),
                            ft.Row([
                                ft.Text(f"Extra: {extra_txt} | {incid_txt}", size=11, color="#475569"),
                                ft.Text(f"📍 {f['origenes']}", size=10.5, color="#00897B", weight=ft.FontWeight.BOLD),
                            ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
                        ], spacing=3)
                    )
                )
        else:
            # Vista RESUMEN MENSUAL (Art. 35.5 ET)
            res_m = resumen_mensual(filas)
            if not res_m:
                contenedor_resultados_consulta.controls.append(
                    ft.Text("No hay datos mensuales para mostrar.", color="#64748B")
                )
            for r in res_m:
                ext_m = fmt_hm(r["extra_s"]) if r["extra_definido"] else "—"
                contenedor_resultados_consulta.controls.append(
                    ft.Container(
                        bgcolor="#EEF2FF",
                        padding=12,
                        border_radius=8,
                        border=ft.border.all(1, "#6366F1"),
                        content=ft.Column([
                            ft.Row([
                                ft.Text(f"🗓 Mes {r['mes']} — [{r['num']}] {r['nombre']}", weight=ft.FontWeight.BOLD, size=13.5),
                                ft.Text(f"Total: {fmt_hm(r['trabajo_s'])}", weight=ft.FontWeight.BOLD, color="#1E40AF"),
                            ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
                            ft.Text(
                                f"Días trabajados: {r['dias']}  |  Horas extra mes: {ext_m}  |  Días con incidencia: {r['incidencias']}",
                                size=12, color="#334155"
                            ),
                        ], spacing=4)
                    )
                )
        page.update()

    def exportar_consulta_actual(_):
        try:
            d_dt = _parse_fecha_filtro(tf_filtro_desde.value)
            h_dt = _parse_fecha_filtro(tf_filtro_hasta.value)
        except ValueError:
            notificar("Fechas inválidas.", "#C62828")
            return
        num_query = (
            sesion_consulta["num_autenticado"]
            if sesion_consulta["modo"] == "EMPLEADO"
            else (None if dd_filtro_emp.value in (None, "TODOS") else dd_filtro_emp.value)
        )
        r_ev, r_res, n_ev, n_mes = exportar_csv_itss(desde=d_dt, hasta=h_dt, num_filtro=num_query)
        dlg = ft.AlertDialog(
            title=ft.Text("📊 Informes CSV Generados"),
            content=ft.Text(
                f"Se han guardado los archivos con los datos sincronizados (Móvil + PC):

"
                f"1. Eventos Sellados ({n_ev} registros):
{r_ev}

"
                f"2. Resumen Mensual Art. 35.5 ET ({n_mes} meses):
{r_res}"
            ),
            actions=[ft.TextButton("Aceptar", on_click=lambda _: page.close(dlg))],
        )
        page.open(dlg)

    panel_controles_consulta.controls = [
        ft.Row([
            ft.ElevatedButton(
                "📋 Detalle por Jornada",
                bgcolor="#1976D2", color="white",
                on_click=lambda _: alternar_subvista_consulta("DIARIO")
            ),
            ft.ElevatedButton(
                "🗓 Resumen Mensual",
                bgcolor="#00897B", color="white",
                on_click=lambda _: alternar_subvista_consulta("MENSUAL")
            ),
            ft.IconButton(icon=ft.icons.LOGOUT, tooltip="Cerrar sesión consulta", on_click=cerrar_sesion_consulta),
        ], spacing=6),
        ft.Row([tf_filtro_desde, tf_filtro_hasta], spacing=8),
        ft.Row([
            dd_filtro_emp,
            ft.ElevatedButton("🔍 Filtrar", bgcolor="#1E40AF", color="white", on_click=refrescar_panel_consultas),
        ], spacing=8),
        lbl_totales_periodo,
        ft.ElevatedButton(
            "📑 Exportar CSV de esta consulta (Eventos + Resumen Mensual)",
            icon=ft.icons.DOWNLOAD, bgcolor="#5E35B1", color="white", on_click=exportar_consulta_actual
        ),
        contenedor_resultados_consulta,
    ]

    # --------------------------------------------------------------------------
    # PESTAÑA 3: CONFIGURACIÓN NUBE (OPCIÓN B SUPABASE) Y GITHUB
    # --------------------------------------------------------------------------
    tf_supa_url = ft.TextField(
        label="URL del Proyecto Supabase (https://xxxx.supabase.co)",
        value=config.get("cloud_supabase_url", ""),
        text_size=12, bgcolor="white"
    )
    tf_supa_key = ft.TextField(
        label="Clave API Pública / Anon Key de Supabase",
        value=config.get("cloud_supabase_anon_key", ""),
        password=True, can_reveal_password=True, text_size=12, bgcolor="white"
    )
    lbl_estado_sincro = ft.Text("Configure su URL de Supabase o descárguela automáticamente de su GitHub.", size=12, color="#334155")

    def guardar_config_nube(_):
        url_s = (tf_supa_url.value or "").strip()
        key_s = (tf_supa_key.value or "").strip()
        config["cloud_supabase_url"] = url_s
        config["cloud_supabase_anon_key"] = key_s
        guardar_configuracion()
        if nube.configurar(url_s, key_s):
            ok_d, msg_d = nube.descargar_nuevos_eventos_a_sqlite()
            cargar_empleados()
            lbl_estado_sincro.value = f"✅ Conectado a Nube: {msg_d}"
            notificar("Sincronización en tiempo real Nube activada.", "#2E7D32")
        else:
            lbl_estado_sincro.value = "⚠️ Nube desactivada (datos guardados solo en local)."
            notificar("Modo local activo.", "#EF6C00")
        refrescar_estado_fichaje()

    def autodescubrir_nube_github(_):
        ok, msg = nube.descubrir_desde_github()
        if ok:
            tf_supa_url.value = nube.supabase_url
            tf_supa_key.value = nube.supabase_key
            config["cloud_supabase_url"] = nube.supabase_url
            config["cloud_supabase_anon_key"] = nube.supabase_key
            guardar_configuracion()
            nube.descargar_nuevos_eventos_a_sqlite()
            cargar_empleados()
        lbl_estado_sincro.value = msg
        refrescar_estado_fichaje()
        notificar(msg, "#2E7D32" if ok else "#EF6C00")

    # --------------------------------------------------------------------------
    # ENSAMBLAJE DE LAS 3 VISTAS PRINCIPALES
    # --------------------------------------------------------------------------
    vista_fichaje = ft.Container(
        padding=14,
        content=ft.Column([
            ft.Container(
                bgcolor="#0F172A", padding=12, border_radius=10,
                content=ft.Column([
                    ft.Row([
                        ft.Text("ACE", size=22, weight=ft.FontWeight.BOLD, color="#60A5FA"),
                        ft.Text("Control Horario Sincronizado", size=13, color="white"),
                    ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
                    lbl_cloud_badge,
                ], spacing=4)
            ),
            ft.Container(
                bgcolor="white", padding=12, border_radius=10, border=ft.border.all(1, "#CBD5E1"),
                content=ft.Column([
                    ft.Row([lbl_reloj], alignment=ft.MainAxisAlignment.CENTER),
                    ft.Row([tf_num, tf_clave], alignment=ft.MainAxisAlignment.CENTER),
                    lbl_estado_actual,
                    lbl_ultimo_origen,
                    ft.TextButton(
                        "📊 Ver Mis Registros / Resumen Mensual (con mi clave)",
                        on_click=ir_directo_a_mis_registros
                    ),
                ], horizontal_alignment=ft.CrossAxisAlignment.CENTER, spacing=6)
            ),
            ft.Row([btn_entrada, btn_salida], spacing=10),
            ft.Row([btn_ini_pausa, btn_fin_pausa], spacing=10),
            ft.OutlinedButton(
                "🔄 Sincronizar estado con PC / Nube ahora",
                icon=ft.icons.SYNC, on_click=refrescar_estado_fichaje
            ),
        ], spacing=10, scroll=ft.ScrollMode.AUTO),
        expand=True,
    )

    vista_consultas = ft.Container(
        padding=14,
        content=ft.Column([
            lbl_cabecera_consulta,
            ft.Container(
                bgcolor="white", padding=10, border_radius=8, border=ft.border.all(1, "#CBD5E1"),
                content=ft.Column([
                    ft.Row([tf_login_cons_num, tf_login_cons_pwd], spacing=6),
                    ft.Row([
                        ft.ElevatedButton("👤 Entrar como Empleado", bgcolor="#00897B", color="white", on_click=login_consulta_empleado),
                        ft.ElevatedButton("🛡️ Entrar como Admin", bgcolor="#FFC107", color="black", on_click=login_consulta_admin),
                    ], spacing=8),
                ], spacing=6)
            ),
            panel_controles_consulta,
        ], spacing=8),
        expand=True,
        visible=False,
    )

    vista_nube = ft.Container(
        padding=14,
        content=ft.Column([
            ft.Text("Sincronización Nube (Opción B) y GitHub", size=16, weight=ft.FontWeight.BOLD),
            ft.Text(
                "Con la Opción B activa, si un trabajador ficha la ENTRADA en el móvil, al llegar al PC verá activo "
                "el botón FICHAR SALIDA al instante, y todas las consultas estarán unificadas.",
                size=11.5, color="#475569"
            ),
            tf_supa_url,
            tf_supa_key,
            ft.Row([
                ft.ElevatedButton("💾 Guardar y Conectar Nube", bgcolor="#2E7D32", color="white", on_click=guardar_config_nube),
                ft.ElevatedButton("☁️ Leer de mi GitHub", bgcolor="#1976D2", color="white", on_click=autodescubrir_nube_github),
            ], spacing=8),
            lbl_estado_sincro,
            ft.Divider(),
            ft.Text(f"Código HW2 de este dispositivo: {codigo_solicitud_equipo()}", size=12, weight=ft.FontWeight.BOLD),
            ft.ElevatedButton(
                "📋 Copiar Código HW2",
                on_click=lambda _: (page.set_clipboard(codigo_solicitud_equipo()), notificar("Código HW2 copiado"))
            ),
        ], spacing=10, scroll=ft.ScrollMode.AUTO),
        expand=True,
        visible=False,
    )

    def cambiar_pestana_manual(idx):
        vista_fichaje.visible = (idx == 0)
        vista_consultas.visible = (idx == 1)
        vista_nube.visible = (idx == 2)
        if idx == 0:
            refrescar_estado_fichaje()
        elif idx == 1:
            refrescar_panel_consultas()
        page.update()

    page.navigation_bar = ft.NavigationBar(
        selected_index=0,
        on_change=lambda e: cambiar_pestana_manual(e.control.selected_index),
        destinations=[
            ft.NavigationDestination(icon=ft.icons.ACCESS_TIME_FILLED, label="Fichar"),
            ft.NavigationDestination(icon=ft.icons.ASSESSMENT, label="Mis Consultas / Admin"),
            ft.NavigationDestination(icon=ft.icons.CLOUD_SYNC, label="Nube / GitHub"),
        ],
    )

    page.add(vista_fichaje, vista_consultas, vista_nube)
    refrescar_estado_fichaje()

    def bucle_reloj_y_sincro():
        contador = 0
        while True:
            time.sleep(1)
            contador += 1
            try:
                lbl_reloj.value = datetime.datetime.now().strftime("%d/%m/%Y  •  %H:%M:%S")
                if contador % 15 == 0 and nube.activo and vista_fichaje.visible:
                    nube.descargar_nuevos_eventos_a_sqlite()
                    refrescar_estado_fichaje()
                else:
                    page.update()
            except Exception:
                break

    threading.Thread(target=bucle_reloj_y_sincro, daemon=True).start()


if __name__ == "__main__":
    ft.app(target=main)
