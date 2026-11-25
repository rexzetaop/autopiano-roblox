#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AutoPiano Roblox
================
Aplicación para reproducir partituras tipo "piano de Roblox".
- Pizarrón INTERACTIVO: se escribe la partitura directo con el teclado
- Toca simultáneamente las letras que estén dentro de ( )  -> acordes
- Ignora símbolos y espacios
- Velocidad y tiempo de tecla mantenida ajustables en la app
- Atajos globales: F8 = Iniciar, F6 = Pausar/Continuar, F7 = Detener
- Analizador de videos: pega links (YouTube, etc.) y extrae la partitura
  de la descripción, subtítulos y comentarios del video
- Búsqueda de partituras en la web: escribí qué buscás (ej: "raining
  tacos roblox sheet") y guardá cada resultado con el nombre que quieras
- Guardar / Nueva / Renombrar / Eliminar partituras directamente en la app

Requiere:  pip install pynput yt-dlp
"""

import colorsys
import glob
import json
import math
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import wave
import webbrowser
import tkinter as tk
from html import unescape as _html_unescape
from tkinter import ttk, filedialog, messagebox, simpledialog, colorchooser

try:
    from pynput import keyboard as pkb
    from pynput.keyboard import Controller as KeyController
    PYNPUT_OK = True
except ImportError:
    PYNPUT_OK = False

# --------------------------------------------------------------------------
# Partituras de ejemplo (se guardan en autopiano_scores.json al primer inicio)
# q=C  w=D  e=E  r=F  t=G  y=A  u=B
# --------------------------------------------------------------------------
DEFAULT_SCORES = {
    "Oda a la Alegría": "w w e r r e w q q w e e w w w w e r r e w q q w e w q q",
    "Estrellita": "q q t t y y t r r e e w w q",
    "Ejemplo con acordes": "(q t y) (w u) e r (q e y) (w u) w e (q t y) q",
}

# Directorio de la app: junto al .py, o junto al AutoPiano.exe si está
# compilado (así los ajustes/partituras siempre van junto al programa)
if getattr(sys, "frozen", False):
    _APP_DIR = os.path.dirname(sys.executable)
else:
    _APP_DIR = os.path.dirname(os.path.abspath(__file__))

SCORES_FILE = os.path.join(_APP_DIR, "autopiano_scores.json")
SETTINGS_FILE = os.path.join(_APP_DIR, "autopiano_settings.json")
SONG_SETTINGS_FILE = os.path.join(_APP_DIR, "autopiano_songsettings.json")
COMPARTIDAS_FILE = os.path.join(_APP_DIR, "autopiano_compartidas.json")
SECCIONES_FILE = os.path.join(_APP_DIR, "autopiano_secciones.json")
COLORES_FILE = os.path.join(_APP_DIR, "autopiano_colores.json")
RECORDS_FILE = os.path.join(_APP_DIR, "autopiano_records.json")
CUENTA_FILE = os.path.join(_APP_DIR, "autopiano_cuenta.json")
ACTIVACION_FILE = os.path.join(_APP_DIR, "autopiano_activacion.json")

# Claves de activación (v4.24): prefijo + 16 caracteres Crockford
CLAVE_PREFIJO = "AP4"
_CLAVE_ALF = "0123456789ABCDEFGHJKMNPQRSTVWXYZ"   # sin I, L, O, U (confusos)
_CLAVE_SECRETO_B64 = "jYoGlYJDZOZehlX1VyOJhmweeko="   # ofuscado (xor 0x5A)
TIPOS_CLAVE = {1: ("semanal", 7), 2: ("mensual", 30),
               3: ("anual", 365), 4: ("permanente", 0),
               5: ("diaria", 1)}
TIPOS_CLAVE_N = {v[0]: k for k, v in TIPOS_CLAVE.items()}

# Registro de claves usadas (v4.25): repo PRIVADO con un permiso acotado
# embebido (sólo Contents: RW de ESE repo). Un solo uso por clave; las
# permanentes NO se registran (exentas).
REGISTRO_REPO = "rexzetaop/claves-usos"
REGISTRO_ARCHIVO = "usadas.txt"
_REG_TOKEN_B64 = ("PTMuMi84BSo7LgVraxkMChBtGRtqaAo3aC0dYm45AwIJBTEeNCkfKTlrYwojNSwVERk"
                  "PDg5iMm84bw8DLxQLOz9iKwkRCWgqCChsKiIcEAICEx0MFAMOCzk2aA4w")  # xor 0x5A

# Anuncio de la clave diaria (v4.25): link del acortador que pone el
# dueño. "" = todavía no hay anuncio configurado (botón "Próximamente").
ANUNCIO_URL = "https://shrtslug.biz/99qXy"
ANUNCIO_ESPERA = 30       # segundos de cuenta regresiva para reclamar

# Paleta de la interfaz: el usuario puede cambiar cada uno (código hex
# tipo #ffffff o con las barras RGB). Se guarda en autopiano_colores.json
# y se aplica recorriendo TODOS los widgets de la app.
COLORES_DEFAULT = {
    "Fondo general": "#2b2b2b",
    "Fondo central (pizarrón)": "#8b5a2b",
    "Fondo de listas": "#1e1e1e",
    "Texto de listas": "#e8e8e8",
    "Texto de acento": "#ffe9c9",
    "Selección": "#4a6da7",
    "Botones": "#5f3f1e",
    "Barra de carpeta": "#6b4a2b",
    "Texto secundario": "#cccccc",
    "Avisos y resaltes": "#ffe066",
}

# Configuración que se guarda en autopiano_settings.json
DEFAULT_SETTINGS = {
    "speed": 1.0,          # multiplicador de velocidad
    "hold_ms": 120,        # ms que la tecla queda apretada
    "realism": 40,         # % de variación humana
    "base_gap": 0.3,       # segundos de separación base entre notas
    "countdown": 3,        # segundos de cuenta regresiva antes de tocar
    "long_note_pct": 18,   # % de notas que se sostienen más (pedal)
    "breathe_pct": 6,      # % de pausas de respiración
    "loop": False,         # repetir la canción en bucle
    "rotate_loop": False,  # en bucle: rotar entre TODAS las partituras
    "importar_preguntado": False,  # ya se preguntó por importar partituras viejas
    "board_font": 13,      # tamaño de letra del pizarrón
    "last_score": "",      # partitura de la última sesión (memoria)
    "last_board": "",      # pizarrón sin guardar de la última sesión
    "practice_mode": False,  # esperar a que el usuario toque cada nota
    "start_cursor": False,   # iniciar desde donde está el cursor
    "compacto_fantasma": False,  # 📌 barra compacta: oculta si el mouse
                                # no está cerca (invisible al transmitir)
}
VIDEO_TMP = os.path.join(tempfile.gettempdir(), "autopiano_video")

LEGENDA = """♻ Reiniciar app — si cambiaste algo del
    programa o salió una versión nueva,
    pulsa aquí: guarda todo y vuelve a
    abrirse con la versión actualizada
    (también te avisa solo cuando detecta
    una versión nueva)

⚙ Ajustes avanzados — cambia TODO con
    números exactos y QUEDA GUARDADO para
    siempre: velocidad, tecla mantenida,
    realismo, separación entre notas,
    cuenta regresiva, % de notas largas,
    % de respiraciones y tamaño del
    pizarrón

🎥 Analizar video — pega links de videos
    (YouTube, TikTok…) y la app extrae la
    partitura de la descripción, los
    subtítulos y los comentarios, o
    TRANSCRIBE EL AUDIO con cualquier
    música/instrumento (casilla 🎹):
    detecta las notas, sus octavas (!) y
    las pausas ( - ) imitando el ritmo

🌐 Buscar notas en la web — escribí lo
    que buscás (ej: "raining tacos
    roblox sheet") y la app busca
    partituras en internet, te muestra
    los resultados y cada uno se guarda
    directo con el nombre que vos quieras

PIZARRÓN — escribe la partitura directo
con el teclado. (Ctrl+S = guardar)

💾 Guardar — guarda lo escrito en la
    partitura seleccionada de la lista;
    si no hay ninguna, te pide un nombre
✏ Nueva — limpia el pizarrón para
    empezar una partitura nueva
⧉ Duplicar — crea una copia de la
    partitura seleccionada (útil para
    probar cambios sin perder la
    original)
⬆/⬇ Octava — sube o baja la octava de
    las letras del pizarrón agregando o
    quitando '!' (no toca los acordes ni
    el formato de piano completo)
🧹 Limpiar — quita símbolos basura de
    texto pegado (|, *, comas…) y
    compacta los espacios
➕/➖ Velocidad en vivo — presiona + o -
    con la canción sonando y cambia la
    velocidad al instante, sin detenerla
🔁 Renombrar — cambia el nombre de la
    partitura seleccionada
🗑 Eliminar — la quita de la lista
🔎 Buscar — escribe en la casilla de
    arriba de la lista y solo se ven las
    partituras que coincidan
📤 Exportar a .txt — guarda la partitura
    seleccionada como archivo para
    compartir con quien quieras
⏱ Duración estimada — junto a las notas
    del pizarrón verás "~m:ss": cuánto
    duraría la canción con tu velocidad
    actual (incluye la cuenta regresiva)

▶ Iniciar (F8) — cuenta regresiva de 3 s
    y toca lo que esté en el pizarrón
⏸ Pausar / ▶ Continuar — congela o
    reanuda (también tecla F6)
⏹ Detener — corta todo (también F7)

Velocidad / Tecla mantenida / Realismo —
    ESCRIBE el número en su casilla y
    presiona Enter (o usa las flechitas).
    TODO se guarda automáticamente y
    queda igual la próxima vez
Tecla mantenida — cuánto suena cada nota;
    la canción SIEMPRE avanza a su ritmo
    (el hold no la frena)
Re-presionar repetidas — SIEMPRE activo
    (sin casilla): si una tecla vuelve a
    salir mientras sigue presionada, se
    suelta y se vuelve a golpear con un
    pequeño aire, así la repetición se
    escucha como nota nueva
☐ Repetir en bucle — la canción se
    repite sola al terminar, con 2 s de
    pausa entre vueltas (ideal para
    practicar). Se guarda automáticamente
☐ Bucle rotando canciones — al terminar
    cada vuelta pasa a la SIGUIENTE
    partitura de la lista y al acabar la
    última vuelve a la primera (activa
    el bucle solo). Se guarda
🎹 Modo práctica (yo toco) — la app no
    toca nada: espera a que PRESIONES TÚ
    cada nota correcta (Roblox la sonará)
    y avanza cuando la sueltes. Para una
    nota repetida, tienes que volver a
    pisarla. Se guarda automáticamente
📍 Iniciar desde el cursor — activa la
    casilla, haz clic en una nota del
    pizarrón y la canción arranca desde
    ahí (ensayar solo una parte)
💾 Respaldo total / 📥 Restaurar —
    guarda o recupera TODAS tus
    partituras y ajustes en un solo
    archivo .json (para cambiar de PC o
    no perder nada nunca)
⚙ Ajustes avanzados — más opciones que
    también se guardan para siempre
    NUEVO: la velocidad, el sostenido y
    el realismo se guardan TAMBIÉN por
    canción: si a una canción le pones
    velocidad 1.5, al volver a ella
    recupera su 1.5 solo (cada canción
    recuerda su config). "Restablecer"
    en el diálogo borra la de la canción
    actual
Realismo — variación aleatoria: cada
    tecla dura un poco distinto (unas más
    largas, otras más cortas), los acordes
    entran y se sueltan con micro-desfases
    y hay pequeñas "respiraciones".
    0% = robot perfecto, 100% = muy humano

Notas dentro de ( ) o [ ] — se tocan
    juntas (acordes, ej: [29g])
Números, mayúsculas y símbolos
    (! @ # $ % ^ & * ( )) — teclas del
    piano completo Virtual Piano/Leqvus;
    las agudas reciben un TOQUE de Shift
    solo en su instante, así los números
    y letras simples del acorde se
    envían sin Shift y no se transforman
Símbolos y espacios — se ignoran
Las teclas van a la ventana activa:
¡deja Roblox en primer plano!"""


# Teclas del piano completo que se tocan con Shift (Virtual Piano/Leqvus):
# ! @ # $ % ^ & * ( )  =  Shift + 1 2 3 4 5 6 7 8 9 0
SHIFT_NOTES = {"!": "1", "@": "2", "#": "3", "$": "4", "%": "5",
               "^": "6", "&": "7", "*": "8", "(": "9", ")": "0"}
VP_CHARS = set(SHIFT_NOTES)          # notas-símbolo del piano completo


def _note_to_key(k):
    """Convierte el token de la partitura en la tecla física a presionar.
    Devuelve (tecla_base, requiere_shift)."""
    if k in SHIFT_NOTES:
        return SHIFT_NOTES[k], True
    if k.isupper():
        return k.lower(), True
    return k, False


def _filtra_notas(s):
    """De un pedazo de texto deja solo caracteres que son notas."""
    return [ch for ch in s
            if ch.isalnum() or ch in VP_CHARS or ch == "^"]


def _canonica(ch):
    """Tecla física canónica de un token, para el modo práctica: así la
    nota '!' (shift+1) coincide cuando el usuario presiona Shift+1, la
    'P' coincide con 'p', y '^' con Shift+6 — antes las notas-símbolo no
    se podían tocar en modo práctica porque se ignoraban."""
    if ch in SHIFT_NOTES:
        return SHIFT_NOTES[ch]
    return ch.lower()


def _escribe_json(path, datos):
    """Escritura ATÓMICA de JSON: primero a un .tmp y luego reemplazo.
    Así un corte de luz o cierre forzado nunca deja el archivo a medias
    (antes, un archivo a medias se cargaba vacío y se perdía todo)."""
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(datos, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def _tokenize_sheet(text: str):
    """Tokeniza la partitura. Devuelve [(inicio, fin, grupo)] con las
    posiciones de cada grupo en el texto (para el resaltado) y el grupo
    es la lista de notas (o ["-"] para pausa).

    Reglas para los delimitadores ( ) [ ]:
    - Acorde pegado: (stf), [ioP], [ips(t] — o con espacios: (q t y), [r u].
      El cierre debe estar cerca (menos de 64 caracteres y 12 notas, misma
      línea): un ')' lejano ya no puede capturar el acorde ni tragarse lo
      que sigue.
    - Abierto sin cerrar PEGADO a notas, ej: '(hddh' -> se CIERRA solo
      (acorde con lo pegado, hasta el primer espacio/delimitador).
    - Abierto por accidente pegado solo a espacios y luego otro
      delimitador o fin de línea, ej: '(   [abd]' -> se IGNORA.
    - '( )' suelto con espacios y notas después, ej: '8 ( e t' -> es la
      NOTA shift+9 / shift+0 del piano completo (no acorde).
    """
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in "([":
            cierre = ")" if c == "(" else "]"
            # buscar el cierre: pegado (stf) o con espacios ((q t y)).
            # NUNCA cruza fin de línea, ni entra en otro delimitador, ni
            # se aleja más de 64 caracteres o 12 notas — así un abierto
            # por accidente ya no puede tragarse medio sheet
            j, ok, notas = i + 1, False, 0
            while j < n and j - i <= 64 and notas <= 12:
                ch = text[j]
                if ch == cierre:
                    ok = True
                    break
                if ch in " \t":
                    j += 1
                    continue
                if ch in "\r\n" or ch == c:
                    break
                if c == "(" and ch in "[]":
                    break           # otro delimitador dentro de ( ): corta
                if ch.isalnum() or ch in VP_CHARS or ch == "^":
                    notas += 1
                j += 1
            if ok:
                inner = _filtra_notas(text[i + 1:j])
                if inner:
                    out.append((i, j + 1, inner))
                i = j + 1
                continue
            # sin cierre válido: cerrar con lo que esté PEGADO (hddh)
            k = i + 1
            while k < n and text[k] not in " \t\r\n()[]":
                k += 1
            inner = _filtra_notas(text[i + 1:k])
            if inner:
                out.append((i, k, inner))       # cerrado forzado
                i = k
            else:
                # pegado solo a espacios: ¿accidente o nota del piano?
                k2 = i + 1
                while k2 < n and text[k2] in " \t":
                    k2 += 1
                if k2 < n and text[k2] in "([":
                    i = i + 1        # '(   [' abierto por accidente: ignorar
                elif (k2 < n and c != "["
                      and (text[k2].isalnum() or text[k2] == "^")):
                    out.append((i, i + 1, [c]))  # nota shift+9 (o shift+0)
                    i += 1
                else:
                    i = i + 1        # fin de línea o símbolo: ignorar
        elif c in ")]":
            # cerrador suelto: ')' puede ser la nota shift+0 si le siguen
            # notas; ']' nunca es nota
            k2 = i + 1
            while k2 < n and text[k2] in " \t":
                k2 += 1
            if (c == ")" and k2 < n
                    and (text[k2].isalnum() or text[k2] == "^")):
                out.append((i, i + 1, [c]))     # nota shift+0
            i += 1
        elif c in "-_":
            out.append((i, i + 1, ["-"]))       # pausa
            i += 1
        elif c == "!":
            # octava alta SOLO si está pegado a la nota (!q); suelto,
            # es la nota shift+1 del piano completo. Acotado: ya no salta
            # espacios ni se come delimitadores que vengan después
            if i + 1 < n and (text[i + 1].isalnum()
                              or text[i + 1] == "^"):
                out.append((i, i + 2, ["!", text[i + 1]]))  # octava alta
                i += 2
            else:
                out.append((i, i + 1, ["!"]))               # nota shift+1
                i += 1
        elif c in "@#$%&*":
            out.append((i, i + 1, [c]))         # nota-símbolo del piano
            i += 1
        elif c.isalnum() or c == "^":
            out.append((i, i + 1, [c]))
            i += 1
        else:
            i += 1  # símbolos y espacios: ignorados
    return out


def parse_sheet(text: str):
    """Convierte el texto de la partitura en una lista de grupos de notas.
    Cada grupo es la lista de teclas que se tocan al mismo tiempo.
    - Letras/dígitos sueltos = una tecla (incluye mayúsculas y números,
      útiles para pianos completos tipo Virtual Piano/Leqvus)
    - Notas dentro de ( ) o [ ] = acorde (todas a la vez); dentro de los
      acordes también cuentan los símbolos del piano completo
      (! @ # $ % ^ & * ( ) = Shift + números)
    - Mayúsculas y símbolos = notas de octava alta (se presionan con un
      toque de Shift en su instante)
    - '!' antes de una letra = octava alta (ej: !q)
    - '-' o '_' solos = pausa (espacio de silencio)
    - '^' = tecla aguda del formato Virtual Piano
    - Delimitadores sin cerrar: '(hddh' se cierra solo; '(   [' se ignora;
      '( )' suelto con notas alrededor es la nota shift+9 / shift+0
    - Cualquier otro símbolo o espacio se ignora
    """
    return [g for _, _, g in _tokenize_sheet(text)]


# ==========================================================================
# Analizador de videos (yt-dlp)
# ==========================================================================
def _find_ytdlp():
    found = shutil.which("yt-dlp") or shutil.which("yt-dlp.exe")
    if found:
        return found
    # buscar yt-dlp.exe junto al programa (instalación manual)
    local = os.path.join(_APP_DIR, "yt-dlp.exe")
    if os.path.exists(local):
        return local
    return None


def _directorios_datos():
    """Carpetas donde buscar datos de una instalación ANTERIOR de AutoPiano
    (para el importador de actualizaciones): Escritorio, Documentos,
    Descargas + sus subcarpetas de primer nivel."""
    home = os.path.expanduser("~")
    bases = [os.path.join(home, "Desktop"),
             os.path.join(home, "Documents"),
             os.path.join(home, "Downloads"),
             os.path.join(home, "OneDrive", "Desktop"),
             os.path.join(home, "OneDrive", "Documents")]
    dirs = list(bases)
    for b in bases:
        try:
            with os.scandir(b) as it:
                for e in it:
                    if e.is_dir():
                        dirs.append(e.path)
        except OSError:
            pass
    return dirs


def _vtt_text(path: str) -> str:
    """Extrae el texto plano de un subtítulo .vtt (quita tiempos y etiquetas)."""
    out = []
    tag = re.compile(r"<[^>]+>")
    try:
        with open(path, "r", encoding="utf-8", errors="ignore") as f:
            for raw in f:
                line = raw.strip()
                if (not line or "-->" in line
                        or line.startswith(("WEBVTT", "Kind:", "Language:", "NOTE"))
                        or line.isdigit()):
                    continue
                line = tag.sub("", line).strip()
                if line and (not out or out[-1] != line):
                    out.append(line)
    except OSError:
        pass
    return " ".join(out)


# Palabras típicas de spam/descripción que no son partitura
_SPAM_WORDS = ("suscrib", "subscribe", "instagram", "discord.gg", "twitter",
               "tiktok.com", "youtube.com", "https", "http", "www.",
               "canal", "like y", "dale like", "comenta", "compartir",
               "derechos", "copyright", "tags:", "#")


def _extract_candidates(text: str):
    """Busca bloques de texto que parezcan partitura (letras, ( ), [ ], ^)."""
    allowed = set("abcdefghijklmnopqrstuvwxyz"
                  "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                  "0123456789()[]|-,*~_^@#$%& \t")
    blocks, cur = [], []
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            if cur:
                blocks.append("\n".join(cur))
                cur = []
            continue
        # una linea de spam separa bloques (no arruina lo que la rodea)
        if any(w in line.lower() for w in _SPAM_WORDS):
            if cur:
                blocks.append("\n".join(cur))
                cur = []
            continue
        alnum = sum(ch.isalnum() for ch in line)
        if alnum >= 4 and all(ch in allowed for ch in line):
            cur.append(line)
        elif cur:
            blocks.append("\n".join(cur))
            cur = []
    if cur:
        blocks.append("\n".join(cur))

    scored = []
    for b in blocks:
        low = b.lower()
        if any(w in low for w in _SPAM_WORDS):
            continue
        alnum = sum(ch.isalnum() for ch in b)
        acordes = b.count("(") + b.count("[")
        agudos = b.count("^")
        # notas del piano simple (q w e r t y u) y mayúsculas de VP/Leqvus
        notas = sum(1 for ch in low if ch in "qwertyu")
        mayus = sum(1 for ch in b if ch.isupper())
        if alnum < 10 and acordes == 0:
            continue
        score = (alnum + acordes * 15 + agudos * 8
                 + notas * 3 + mayus * 2)
        scored.append((score, b))
    scored.sort(key=lambda x: x[0], reverse=True)
    return [b for _, b in scored]


def _find_ffmpeg():
    here = os.path.dirname(os.path.abspath(__file__))
    for name in ("ffmpeg.exe", "ffmpeg"):
        p = os.path.join(here, name)
        if os.path.exists(p):
            return p
    return shutil.which("ffmpeg") or shutil.which("ffmpeg.exe")


def _video_title(url: str) -> str:
    ytdlp = _find_ytdlp()
    if not ytdlp:
        return "Video"
    try:
        r = subprocess.run([ytdlp, "--skip-download", "--print", "title",
                            "--no-playlist", url],
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace", timeout=90)
        lines = [l.strip() for l in (r.stdout or "").splitlines() if l.strip()]
        return lines[-1] if lines else "Video"
    except Exception:
        return "Video"


def _download_audio(url: str) -> str:
    """Descarga solo el audio del video con yt-dlp. Devuelve la ruta."""
    os.makedirs(VIDEO_TMP, exist_ok=True)
    for f in glob.glob(os.path.join(VIDEO_TMP, "audio.*")):
        try:
            os.remove(f)
        except OSError:
            pass
    ytdlp = _find_ytdlp()
    if not ytdlp:
        raise RuntimeError("yt-dlp no está disponible")
    cmd = [ytdlp, "-f", "bestaudio[ext=m4a]/bestaudio", "--no-playlist",
           "-o", os.path.join(VIDEO_TMP, "audio.%(ext)s"), url]
    r = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                       errors="replace", timeout=300)
    files = [f for f in glob.glob(os.path.join(VIDEO_TMP, "audio.*"))
             if not f.endswith(".part")]
    if not files:
        raise RuntimeError(f"yt-dlp no pudo descargar el audio: "
                           f"{(r.stderr or '')[-200:]}")
    return files[0]


def _to_wav_16k(src: str) -> str:
    """Convierte cualquier audio a WAV mono 16 kHz con ffmpeg."""
    ff = _find_ffmpeg()
    if not ff:
        raise RuntimeError("Falta ffmpeg.exe junto a la app (para leer el audio)")
    wav = os.path.join(VIDEO_TMP, "audio16k.wav")
    if os.path.exists(wav):
        os.remove(wav)
    cmd = [ff, "-y", "-i", src, "-vn", "-ac", "1", "-ar", "16000",
           "-acodec", "pcm_s16le", wav]
    subprocess.run(cmd, capture_output=True, timeout=300, check=True)
    return wav


# ==========================================================================
# Transcriptor de audio -> partitura (numpy, sin servicios externos)
# ==========================================================================
_WHITE_PC = (0, 2, 4, 5, 7, 9, 11)
_WHITE_LETTER = {0: "q", 2: "w", 4: "e", 5: "r", 7: "t", 9: "y", 11: "u"}


def _read_wav_mono(path: str):
    import numpy as np
    with wave.open(path, "rb") as w:
        sr = w.getframerate()
        ch = w.getnchannels()
        raw = w.readframes(w.getnframes())
    x = np.frombuffer(raw, dtype=np.int16).astype(np.float64) / 32768.0
    if ch > 1:
        x = x.reshape(-1, ch).mean(axis=1)
    return sr, x


def _fold_white(midi: int) -> int:
    """Aproxima una nota cualquiera a la tecla blanca más cercana."""
    pc = midi % 12
    best = min(_WHITE_PC, key=lambda p: min(abs(p - pc), 12 - abs(p - pc)))
    return midi - pc + best


def _midi_to_token(midi: int) -> str:
    midi = _fold_white(int(midi))
    letter = _WHITE_LETTER[midi % 12]
    rel = midi - 60                       # C4 = "q"
    if 0 <= rel < 12:
        return letter
    if 12 <= rel < 24:
        return "!" + letter               # octava alta del piano de Roblox
    return letter                         # fuera de rango: se pliega


def transcribe_audio(wav_path: str, progress=None) -> str:
    """Analiza el WAV y devuelve una partitura con notas, octavas (!) y
    pausas ( - ) que imitan los espacios del audio original.

    Técnica: STFT + separación armónico/percusivo (elimina metrónomo y
    golpes), banda de melodía, detección de tonalidad (las notas se ajustan
    a la escala de la canción) y re-ataques para notas repetidas."""
    import numpy as np
    sr, x = _read_wav_mono(wav_path)
    frame_len = 4096                      # 256 ms de ventana
    hop = 512                             # 32 ms de resolución temporal
    f_min, f_max = 130.0, 1100.0          # banda de melodía (fuera el bajo)
    if len(x) < frame_len:
        return ""
    n_frames = (len(x) - frame_len) // hop + 1
    win = np.hanning(frame_len).astype(np.float32)
    freqs = np.fft.rfftfreq(frame_len, 1.0 / sr)
    k_min = int(np.searchsorted(freqs, f_min))
    k_max = int(np.searchsorted(freqs, f_max))
    nbins = k_max + 1

    # ---- STFT completa (float32) ------------------------------------------
    S = np.empty((n_frames, nbins), dtype=np.float32)
    rms = np.empty(n_frames)
    for i in range(n_frames):
        seg = x[i * hop: i * hop + frame_len]
        S[i] = np.abs(np.fft.rfft(seg * win))[:nbins]
        rms[i] = np.sqrt(np.mean(seg ** 2))
        if progress and (i % 40 == 0):
            progress(i / n_frames * 0.6)

    # ---- separación armónico/percusivo ------------------------------------
    # mediana a lo largo del TIEMPO: las notas sostenidas sobreviven, los
    # golpes (metrónomo, batería) desaparecen
    pad = 4
    S_pad = np.pad(S, ((pad, pad), (0, 0)), mode="edge")
    stack = np.stack([S_pad[j: j + n_frames] for j in range(2 * pad + 1)])
    S_harm = np.median(stack, axis=0).astype(np.float32)
    del stack, S_pad

    eharm = np.sqrt(np.mean(S_harm[:, k_min:nbins] ** 2, axis=1))
    silencio = eharm < max(eharm.max() * 0.06, 1e-4)

    # ---- pitch por frame: línea de MELODÍA (la voz superior) ---------------
    # Los tutoriales/arreglos tocan melodía (agudos) + acompañamiento
    # (graves). Para que suene a la canción, elegimos el pico más AGUDO que
    # siga siendo fuerte, corrigiendo errores de octava.
    midi_f = np.zeros(n_frames)
    mag_f = np.zeros(n_frames)
    for i in range(n_frames):
        if silencio[i]:
            continue
        m = S_harm[i]
        mmax = m[k_min:nbins].max() + 1e-12
        # picos locales fuertes en magnitud cruda
        candidatos = []
        for kb in range(k_min + 1, nbins - 1):
            if m[kb] >= m[kb - 1] and m[kb] >= m[kb + 1] and m[kb] >= 0.30 * mmax:
                candidatos.append(kb)
        if not candidatos:
            continue
        # corrección de octava: solo descartar si el sub-armónico es casi
        # tan fuerte (si no, probablemente es una nota real de la mano izq.)
        buenos = []
        for kb in candidatos:
            falso = False
            for div, umbral in ((2, 0.7), (3, 0.5)):
                kb2 = int(round(kb / div))
                if k_min <= kb2 < nbins and m[kb2] >= umbral * m[kb]:
                    falso = True
                    break
            if not falso:
                buenos.append(kb)
        if not buenos:
            continue
        # selección con continuidad: la melodía es una línea fluida, no
        # saltos aleatorios. Base = fuerza del pico + bonus si sigue cerca
        # de la nota anterior, penalización si da un salto de octava enorme.
        prev = midi_f[i - 1] if i > 0 else 0.0
        mejor_kb, mejor_val = None, -1e9
        for kb in buenos:
            f = kb * freqs[1]
            midi = 69.0 + 12.0 * np.log2(f / 440.0)
            val = m[kb] / mmax
            if prev:
                diff = abs(midi - prev)
                if diff <= 2:
                    val += 0.25
                elif diff > 12:
                    val -= 0.35
            if val > mejor_val:
                mejor_val, mejor_kb = val, kb
        kb = mejor_kb
        entorno = np.median(m[max(k_min, kb - 6): kb + 7]) + 1e-12
        if m[kb] < entorno * 1.6:
            continue
        # interpolación parabólica del pico (frecuencia más exacta)
        a, b, c = m[kb - 1], m[kb], m[kb + 1]
        d = a - 2 * b + c
        delta = 0.5 * (a - c) / d if abs(d) > 1e-12 else 0.0
        delta = max(-0.5, min(0.5, delta))
        f = (kb + delta) * freqs[1]
        midi_f[i] = 69.0 + 12.0 * np.log2(f / 440.0)
        mag_f[i] = m[kb]
        if progress and i % 40 == 0:
            progress(0.6 + i / n_frames * 0.3)

    # ---- tonalidad: histograma de alturas y mejor escala -------------------
    hist = np.zeros(12)
    activos = midi_f > 0
    if activos.any():
        pcs = ((np.round(midi_f[activos]).astype(int)) % 12)
        for pc, mg in zip(pcs, mag_f[activos]):
            hist[pc % 12] += mg
        mejor, mejor_pc = None, -1.0
        for root in range(12):
            for nombre, plantilla in (
                    ("mayor", (0, 2, 4, 5, 7, 9, 11)),
                    ("menor", (0, 2, 3, 5, 7, 8, 10))):
                sc = sum(hist[(root + t) % 12] for t in plantilla)
                if sc > mejor_pc:
                    mejor_pc, mejor = sc, {(root + t) % 12 for t in plantilla}
        escala = mejor if mejor else {0, 2, 4, 5, 7, 9, 11}
    else:
        escala = {0, 2, 4, 5, 7, 9, 11}

    def snap_escala(midi):
        pc = int(round(midi)) % 12
        if pc in escala:
            return midi
        # llevar la nota a la altura de la escala más cercana
        dists = [(min((p - pc) % 12, (pc - p) % 12), p) for p in escala]
        _, p = min(dists)
        delta = (p - pc + 6) % 12 - 6          # -5..+6 semitonos
        return midi + delta

    for i in range(n_frames):
        if midi_f[i]:
            midi_f[i] = snap_escala(midi_f[i])

    # ---- suavizado por mayoría ---------------------------------------------
    sm = midi_f.copy()
    for i in range(n_frames):
        if midi_f[i]:
            vec = [midi_f[k] for k in range(max(0, i - 1), min(n_frames, i + 2))
                   if midi_f[k]]
            sm[i] = max(set(vec), key=vec.count)

    # ---- eventos: tramos con la misma nota + re-ataques --------------------
    events = []
    i = 0
    while i < n_frames:
        if sm[i] == 0:
            i += 1
            continue
        j = i
        run_max = eharm[i]
        while j < n_frames and abs(sm[j] - sm[i]) < 0.7:
            run_max = max(run_max, eharm[j])
            # re-ataque: la energía sube de golpe → nota repetida
            if (j > i + 2 and eharm[j] > 1.4 * min(eharm[j - 4:j])
                    and eharm[j] > 0.5 * run_max):
                break
            j += 1
        if j - i >= 3:                     # dura al menos ~96 ms
            m = int(round(float(np.median(sm[i:j]))))
            events.append([m, i * hop / sr, j * hop / sr])
        i = max(j, i + 1)
    if progress:
        progress(1.0)
    if not events:
        return ""

    # fusionar la misma nota si solo se separó por un gap minúsculo
    merged = [events[0]]
    for ev in events[1:]:
        last = merged[-1]
        if ev[0] == last[0] and ev[1] - last[2] < 0.12:
            last[2] = ev[2]
        else:
            merged.append(ev)

    # convertir a partitura: cada hueco entre notas se representa con pausas
    rest_unit = 0.25                       # cada " - " ≈ 0.25 s de silencio
    parts = []
    prev_end = None
    for m, t0, t1 in merged:
        if prev_end is not None:
            n_rest = int(round((t0 - prev_end) / rest_unit))
            if n_rest > 0:
                parts.append(" - " * min(n_rest, 12))
        parts.append(_midi_to_token(m))
        prev_end = t1
    return " ".join(parts)


def _fetch_video(url: str, use_comments: bool):
    """Descarga descripción + subtítulos (+ comentarios) del video con yt-dlp.
    Devuelve (título, texto_para_buscar)."""
    os.makedirs(VIDEO_TMP, exist_ok=True)
    for f in glob.glob(os.path.join(VIDEO_TMP, "videoinfo*")):
        try:
            os.remove(f)
        except OSError:
            pass
    ytdlp = _find_ytdlp()
    if not ytdlp:
        raise RuntimeError("yt-dlp no está instalado. Ejecuta:  pip install yt-dlp")

    cmd = [ytdlp, "--skip-download", "--write-description",
           "--write-auto-subs", "--write-subs", "--sub-langs", "es.*,en.*",
           "--convert-subs", "vtt",
           "-o", "videoinfo.%(ext)s", url]
    subprocess.run(cmd, cwd=VIDEO_TMP, capture_output=True, text=True,
                   encoding="utf-8", errors="replace", timeout=120)
    title = _video_title(url)

    blob = ""
    desc_path = os.path.join(VIDEO_TMP, "videoinfo.description")
    if os.path.exists(desc_path):
        with open(desc_path, "r", encoding="utf-8", errors="ignore") as f:
            blob += f.read() + "\n"
    for v in glob.glob(os.path.join(VIDEO_TMP, "videoinfo.*.vtt")):
        blob += _vtt_text(v) + "\n"

    if use_comments:
        cmd2 = [ytdlp, "-J", "--write-comments", "--extractor-args",
                "youtube:max_comments=120,all,50", url]
        try:
            r2 = subprocess.run(cmd2, capture_output=True, text=True,
                                encoding="utf-8", errors="replace", timeout=180)
            data = json.loads(r2.stdout or "{}")
            title = data.get("title", title)
            for c in data.get("comments", []):
                blob += "\n" + (c.get("text") or "")
        except Exception:
            pass

    return title, blob


# ==========================================================================
# Actualización automática por internet (GitHub)
# ==========================================================================
# Repo público donde viven la última versión y los archivos para bajar.
# ACTUALIZACION_REPO vacío = comprobación desactivada (tests / locales).
ACTUALIZACION_REPO = "rexzetaop/autopiano-roblox"   # repo público en GitHub


def _act_urls():
    """URLs de actualización; (None, None) si no hay repo configurado."""
    if not ACTUALIZACION_REPO:
        return None, None
    base = "https://raw.githubusercontent.com/" + ACTUALIZACION_REPO
    return (base + "/main/version.txt",
            base + "/main/autopiano.py")


def _version_a_tupla(v: str):
    """'4.22' -> (4, 22) para comparar; basura -> (0,)."""
    nums = re.findall(r"\d+", v or "")
    return tuple(int(n) for n in nums) if nums else (0,)


def _version_remota() -> str:
    """Lee version.txt del repo. Devuelve '4.22' o '' si no hay nada
    (sin internet, sin repo configurado… nunca lanza excepción)."""
    url, _ = _act_urls()
    if not url:
        return ""
    try:
        txt = _web_http_get(url, timeout=15).strip()
        return txt.splitlines()[0].strip() if txt else ""
    except Exception:
        return ""


def _hay_actualizacion(remota: str, local: str) -> bool:
    """¿La versión remota es MAYOR que la local?"""
    if not remota:
        return False
    try:
        return _version_a_tupla(remota) > _version_a_tupla(local)
    except Exception:
        return False


def _descargar_actualizacion(url: str, destino: str, avance=None) -> str:
    """Descarga un archivo (bytes) a 'destino' con avance de %.
    Devuelve la ruta. Lanza si la descarga es sospechosamente chica
    (página de error en vez del archivo)."""
    import urllib.request
    req = urllib.request.Request(url, headers={"User-Agent": _WEB_UA})
    with urllib.request.urlopen(req, timeout=60) as resp:
        total = int(resp.headers.get("Content-Length") or 0)
        chunks = []
        leido = 0
        while True:
            trozo = resp.read(65536)
            if not trozo:
                break
            chunks.append(trozo)
            leido += len(trozo)
            if avance and total:
                avance(min(leido / total, 1.0))
    datos = b"".join(chunks)
    if len(datos) < 1024:
        raise RuntimeError("la descarga vino vacía o incompleta")
    if total and leido != total:
        # el servidor prometió N bytes y llegaron menos: cortada a la
        # mitad (red inestable). Mejor NO tocar la instalación actual.
        raise RuntimeError(f"descarga incompleta: {leido} de {total} bytes")
    with open(destino, "wb") as f:
        f.write(datos)
    return destino


def _validar_descarga(ruta: str, es_exe: bool) -> None:
    """Comprueba que lo descargado sea de verdad el programa y no una
    página de error, un HTML de 404 o un archivo cortado a la mitad.
    Sin esto, una mala descarga pisaba el exe bueno y la app quedaba
    sin funcionar (tenía que reinstalarse a mano). Si falla, LANZA y
    el caller NO cierra la app: se sigue usando la versión actual."""
    tam = os.path.getsize(ruta)
    if es_exe:
        with open(ruta, "rb") as f:
            cab = f.read(2)
        # todo .exe de Windows empieza con "MZ"; un HTML o JSON nunca
        if cab != b"MZ" or tam < 65536:
            raise RuntimeError("lo descargado no es un .exe válido")
        return
    try:
        with open(ruta, "r", encoding="utf-8") as f:
            texto = f.read()
    except UnicodeDecodeError:
        raise RuntimeError("lo descargado no es código Python válido") \
            from None
    if "AutoPiano" not in texto:
        raise RuntimeError("lo descargado no es el código de AutoPiano")
    try:
        compile(texto, ruta, "exec")
    except SyntaxError:
        raise RuntimeError("el código descargado está incompleto o corrupto") \
            from None


def _helper_actualizacion(nuevo: str, actual: str) -> str:
    """Crea el .bat que espera a que la app cierre, reemplaza el
    archivo y vuelve a abrir. Devuelve su ruta (para lanzarlo).

    El .bat:
    1) espera a que el proceso termine de cerrar (nombre EMBEBIDO:
       antes se usaba %~nx1 sin pasarle argumentos, el filtro quedaba
       vacío y NO esperaba nada — se copiaba contra el exe en uso);
    2) si el archivo nuevo no está (p. ej. lo borró el antivirus),
       no toca nada y reabre el actual;
    3) guarda un .bak del actual y, si la copia queda más chica que
       el origen (cortada a mitad), lo restaura: así nunca queda un
       exe a medias que no arranca."""
    bat = os.path.join(tempfile.gettempdir(), "autopiano_actualiza.bat")
    exe_nombre = os.path.basename(actual) or "AutoPiano.exe"
    lineas = [
        "@echo off",
        "chcp 65001 >nul",
        # esperar a que AutoPiano termine de cerrar (máx. 60 s)
        "set /a espera=0",
        ":esperar",
        "timeout /t 1 /nobreak >nul",
        "set /a espera+=1",
        f'tasklist /fi "imagename eq {exe_nombre}" 2>nul'
        f' | find /i "{exe_nombre}" >nul',
        "if not errorlevel 1 if %espera% lss 60 goto esperar",
        # sin archivo nuevo no hay nada que copiar: quedarse con el actual
        f'if not exist "{nuevo}" goto abrir',
        # respaldo del actual por si la copia sale a medias
        f'copy /y "{actual}" "{actual}.bak" >nul',
        # reemplazar (con reintentos por si aún está bloqueado)
        "set /a intentos=0",
        ":copiar",
        f'copy /y "{nuevo}" "{actual}" >nul',
        "if errorlevel 1 (",
        "  set /a intentos+=1",
        "  timeout /t 1 /nobreak >nul",
        "  if %intentos% lss 10 goto copiar",
        ")",
        # la copia debe haber quedado completa (no más chica que el
        # origen): si no, restaurar el respaldo
        'set "szn=0"',
        'set "sza=0"',
        f'for %%A in ("{nuevo}") do set "szn=%%~zA"',
        f'for %%A in ("{actual}") do set "sza=%%~zA"',
        f'if %sza% LSS %szn% copy /y "{actual}.bak" "{actual}" >nul',
        f'del "{actual}.bak" >nul 2>nul',
        ":abrir",
        f'start "" "{actual}"',
        'del "%~f0"',
    ]
    with open(bat, "w", encoding="utf-8", errors="replace") as f:
        f.write("\r\n".join(lineas) + "\r\n")
    return bat


def _reemplazar_y_reiniciar(nuevo: str):
    """Reemplaza el programa por 'nuevo' y reinicia la app.
    - Ejecutable (PyInstaller): Windows no deja sobrescribirse a sí
      mismo en marcha, así que un .bat espera al cierre, copia y reabre.
    - Archivo .py: Python no lo bloquea: se sobrescribe directo y la
      app ya existente ♻ Reiniciar lo detecta al instante."""
    actual = os.path.abspath(sys.executable if getattr(sys, "frozen", False)
                             else __file__)
    if getattr(sys, "frozen", False):
        bat = _helper_actualizacion(nuevo, actual)
        subprocess.Popen(["cmd", "/c", bat], creationflags=0x08000000)
        return "reinicio"
    # reemplazo ATÓMICO: primero a un .nuevo y recién ahí se reemplaza
    # (así un corte a mitad de escritura no deja el .py a medias)
    tmp = actual + ".nuevo"
    try:
        shutil.copyfile(nuevo, tmp)
        os.replace(tmp, actual)
    finally:
        if os.path.exists(tmp):
            try:
                os.remove(tmp)
            except OSError:
                pass
    return "archivo"


def _actualizar_internet(avance=None) -> str:
    """Flujo completo: verifica versión remota, descarga y reemplaza.
    Devuelve: 'sin-repo' | 'sin-version' | 'actualizado' | 'al-dia'."""
    url_ver, url_py = _act_urls()
    if not url_ver:
        return "sin-repo"
    remota = _version_remota()
    if not remota:
        return "sin-version"
    if not _hay_actualizacion(remota, AutoPianoApp.VERSION):
        return "al-dia"
    con_exe = getattr(sys, "frozen", False)
    url = (None if con_exe else url_py)
    if con_exe:
        url = ("https://github.com/" + ACTUALIZACION_REPO
               + "/releases/latest/download/AutoPiano.exe")
    destino = os.path.join(tempfile.gettempdir(),
                           "AutoPiano_nuevo.exe" if con_exe
                           else "autopiano_nuevo.py")
    _descargar_actualizacion(url, destino, avance=avance)
    # sólo reemplazar si lo descargado es realmente el programa
    # (si no, la app seguiría funcionando con la versión actual)
    _validar_descarga(destino, con_exe)
    _reemplazar_y_reiniciar(destino)
    return "actualizado"


# ==========================================================================
# Búsqueda de partituras en la web
# ==========================================================================
_WEB_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
           "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")


def _web_http_get(url: str, timeout: int = 20) -> str:
    """Descarga una página web con urllib (sin librerías extra) y
    devuelve el HTML como texto."""
    import urllib.request
    req = urllib.request.Request(url, headers={
        "User-Agent": _WEB_UA,
        "Accept": "text/html,application/xhtml+xml,*/*;q=0.8",
        "Accept-Language": "es-419,es;q=0.9,en;q=0.6"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        raw = resp.read()
        try:
            charset = resp.headers.get_content_charset()
        except Exception:
            charset = None
    return raw.decode(charset or "utf-8", errors="replace")


# ======================================================================
# v4.23 — Nube de partituras, canciones de la comunidad y récords
# ======================================================================
GITHUB_API = "https://api.github.com"
NUBE_GIST_NOMBRE = "AutoPiano - mis partituras"
COMUNIDAD_DIR = "partituras"       # carpeta de canciones en el repo
COMUNIDAD_REPO = ACTUALIZACION_REPO


def _github_api(ruta: str, metodo: str = "GET", cuerpo: dict = None,
                token: str = None):
    """Llamada a la API de GitHub. Devuelve el dict/objeto JSON o None si
    algo falla (sin excepciones hacia arriba). `ruta` es p.ej.
    "repos/x/y/contents/archivo" (sin /repos/ inicial)."""
    import urllib.request
    url = f"{GITHUB_API}/{ruta.lstrip('/')}"
    data = None
    if cuerpo is not None:
        data = json.dumps(cuerpo).encode("utf-8")
    encabezados = {"User-Agent": _WEB_UA,
                   "Accept": "application/vnd.github+json"}
    if token:
        encabezados["Authorization"] = f"Bearer {token}"
    try:
        req = urllib.request.Request(url, data=data, method=metodo,
                                     headers=encabezados)
        with urllib.request.urlopen(req, timeout=30) as resp:
            texto = resp.read().decode("utf-8", errors="replace")
        try:
            return json.loads(texto) if texto else {}
        except Exception:
            return texto
    except Exception:
        return None


def _gh_token():
    """Token de GitHub del usuario, si existe: primero autopiano_cuenta.json
    ({"token": ...}), después el Administrador de credenciales de Windows
    donde gh CLI dejó el suyo (target gh:github.com:...). "" si no hay."""
    try:
        if os.path.exists(CUENTA_FILE):
            with open(CUENTA_FILE, "r", encoding="utf-8-sig") as f:
                tok = (json.load(f) or {}).get("token")
            if isinstance(tok, str) and tok.strip():
                return tok.strip()
    except Exception:
        pass
    try:
        import ctypes
        from ctypes import wintypes

        class CREDENTIAL(ctypes.Structure):
            _fields_ = [("Flags", wintypes.DWORD),
                        ("Type", wintypes.DWORD),
                        ("TargetName", wintypes.LPWSTR),
                        ("Comment", wintypes.LPWSTR),
                        ("LastWritten", wintypes.FILETIME),
                        ("CredentialBlobSize", wintypes.DWORD),
                        ("CredentialBlob",
                         ctypes.POINTER(ctypes.c_ubyte)),
                        ("Persist", wintypes.DWORD),
                        ("AttributeCount", wintypes.DWORD),
                        ("Attributes", ctypes.c_void_p),
                        ("TargetAlias", wintypes.LPWSTR),
                        ("UserName", wintypes.LPWSTR)]
        advapi = ctypes.windll.advapi32
        n = wintypes.DWORD()
        pp = ctypes.POINTER(ctypes.POINTER(CREDENTIAL))()
        if advapi.CredEnumerateW("gh:*", 0, ctypes.byref(n),
                                 ctypes.byref(pp)):
            mejor, fecha = "", 0
            for i in range(n.value):
                c = pp[i].contents
                blob = ctypes.string_at(c.CredentialBlob,
                                        c.CredentialBlobSize)
                tok = blob.decode("utf-8", "ignore").strip()
                escrito = (c.LastWritten.dwHighDateTime << 32
                           | c.LastWritten.dwLowDateTime)
                if tok.startswith("gh") and escrito > fecha:
                    mejor, fecha = tok, escrito
            advapi.CredFree(pp)
            return mejor
    except Exception:
        pass
    return ""


def _nube_archivos():
    """Los 4 json que forman 'mis partituras' (sin settings global:
    esa se queda en cada PC, que tiene teclado/pantalla distintos)."""
    return [("autopiano_scores.json", SCORES_FILE),
            ("autopiano_songsettings.json", SONG_SETTINGS_FILE),
            ("autopiano_secciones.json", SECCIONES_FILE),
            ("autopiano_colores.json", COLORES_FILE)]


def _nube_gist(token):
    """Busca el gist privado de la nube; lo crea si no existe.
    Devuelve el id o ""."""
    import urllib.request
    try:
        req = urllib.request.Request(
            f"{GITHUB_API}/gists", method="GET",
            headers={"User-Agent": _WEB_UA,
                     "Authorization": f"Bearer {token}"})
        with urllib.request.urlopen(req, timeout=30) as gists:
            lista = json.loads(gists.read().decode("utf-8", "replace"))
        for g in lista if isinstance(lista, list) else []:
            if g.get("description") == NUBE_GIST_NOMBRE:
                return g.get("id", "")
    except Exception:
        return ""
    cuerpo = {"description": NUBE_GIST_NOMBRE, "public": False,
              "files": {"README.md": {"content":
                       "Partituras de AutoPiano (respaldo automatico)."}}}
    res = _github_api("gists", "POST", cuerpo, token)
    return res.get("id", "") if isinstance(res, dict) else ""


def nube_subir():
    """Sube los json al gist privado. Devuelve "ok", "sin-token",
    "sin-gist" o "error"."""
    token = _gh_token()
    if not token:
        return "sin-token"
    gid = _nube_gist(token)
    if not gid:
        return "sin-gist"
    files = {}
    for nombre, ruta in _nube_archivos():
        try:
            with open(ruta, "r", encoding="utf-8-sig") as f:
                contenido = f.read()
        except Exception:
            contenido = json.dumps({}, ensure_ascii=False)
        files[nombre] = {"content": contenido}
    res = _github_api(f"gists/{gid}", "PATCH",
                      {"files": files}, token)
    return "ok" if res is not None else "error"


def nube_bajar():
    """Descarga los json del gist privado y los deja en la carpeta de la
    app. Los actuales se guardan antes con sufijo .pre-nube-FECHA (por si
    querés volver atrás). Devuelve "ok", "sin-token", "sin-gist",
    "vacio" o "error"."""
    token = _gh_token()
    if not token:
        return "sin-token"
    gid = _nube_gist(token)
    if not gid:
        return "sin-gist"
    datos = _github_api(f"gists/{gid}", "GET", None, token)
    if not isinstance(datos, dict):
        return "error"
    archivos = datos.get("files") or {}
    bajados = 0
    fecha = time.strftime("%Y%m%d")
    for nombre, ruta in _nube_archivos():
        info = archivos.get(nombre)
        contenido = (info or {}).get("content")
        if not isinstance(contenido, str):
            continue
        try:
            if os.path.exists(ruta):
                shutil.copyfile(ruta, f"{ruta}.pre-nube-{fecha}")
        except Exception:
            pass
        try:
            json.loads(contenido)          # sólo json válidos
            with open(ruta, "w", encoding="utf-8") as f:
                f.write(contenido)
            bajados += 1
        except Exception:
            continue
    if not bajados:
        return "vacio"
    # secciones y colores viven en memoria: recargar
    return "ok"


def comunidad_listar():
    """Lista las partituras compartidas en la carpeta del repo.
    Devuelve [(nombre, download_url)] o [] (sin red/error)."""
    res = _github_api(f"repos/{COMUNIDAD_REPO}/contents/{COMUNIDAD_DIR}")
    if not isinstance(res, list):
        return []
    out = []
    for item in res:
        if (isinstance(item, dict) and item.get("type") == "file"
                and item.get("name", "").lower().endswith(".txt")):
            out.append((item["name"], item.get("download_url") or ""))
    out.sort()
    return out


def comunidad_leer(download_url):
    """Descarga una partitura de la comunidad (texto plano). "" si falla."""
    if not download_url:
        return ""
    try:
        return _web_http_get(download_url, timeout=20)
    except Exception:
        return ""


def comunidad_subir(nombre, texto):
    """Sube una partitura a la carpeta del repo (dueño de la cuenta).
    Devuelve "ok", "sin-token" o "error"."""
    import base64
    token = _gh_token()
    if not token:
        return "sin-token"
    if not nombre.lower().endswith(".txt"):
        nombre += ".txt"
    nombre = "".join(ch for ch in nombre
                     if ch.isalnum() or ch in " ._-()áéíóúÁÉÍÓÚñÑ")
    ruta = f"repos/{COMUNIDAD_REPO}/contents/{COMUNIDAD_DIR}/{nombre}"
    cuerpo = {"message": f"Partitura de la comunidad: {nombre}",
              "content": base64.b64encode(
                  texto.encode("utf-8")).decode("ascii")}
    previo = _github_api(ruta)         # ¿ya existe? -> hace falta el sha
    if isinstance(previo, dict) and previo.get("sha"):
        cuerpo["sha"] = previo["sha"]
    res = _github_api(ruta, "PUT", cuerpo, token)
    return "ok" if isinstance(res, dict) else "error"


# ======================================================================
# v4.24 — 🗝 Claves de activación (semanal / mensual / anual / permanente)
# ======================================================================
CLAVES_REPO = "rexzetaop/autopiano-roblox"   # donde vive claves_revocadas.txt


def _clave_secreto():
    """Secreto de firmado (ofuscado con xor 0x5A en la constante)."""
    import base64
    return bytes(b ^ 0x5A for b in base64.b64decode(_CLAVE_SECRETO_B64))


def _clave_mac(datos):
    """Firma HMAC-SHA256 de los primeros 6 bytes, recortada a 4."""
    import hashlib
    import hmac
    return hmac.new(_clave_secreto(), datos, hashlib.sha256).digest()[:4]


def _crock_enc(datos: bytes) -> str:
    """Base32 Crockford: 10 bytes -> exactamente 16 caracteres."""
    bits = int.from_bytes(datos, "big")
    total = len(datos) * 8
    out = []
    for i in range(total // 5):
        out.append(_CLAVE_ALF[(bits >> (total - 5 * (i + 1))) & 31])
    return "".join(out)


def _crock_dec(texto: str) -> bytes:
    """Inversa de _crock_enc; lanza ValueError con caracteres raros."""
    if len(texto) % 8 == 0 and texto.endswith("="):
        texto = texto.rstrip("=")
    val = 0
    for ch in texto:
        i = _CLAVE_ALF.find(ch)
        if i < 0:
            raise ValueError("caracter invalido")
        val = (val << 5) | i
    bits = len(texto) * 5
    return val.to_bytes(bits // 8, "big") if bits % 8 == 0 else \
        val.to_bytes(bits // 8 + 1, "big")[1:]


def clave_normalizar(texto):
    """Mayúsculas, sin símbolos, y con las confusiones usuales resueltas
    (O→0, I/L→1: esos símbolos no existen en el alfabeto de la clave)."""
    import re
    t = re.sub(r"[^0-9A-Za-z]", "", (texto or "")).upper()
    return t.replace("O", "0").replace("I", "1").replace("L", "1")


def clave_generar(tipo):
    """Crea una clave nueva firmada. tipo: nombre ('semanal', 'mensual',
    'anual', 'permanente', 'diaria') o número 1-5. El reloj arranca al
    ACTIVAR (la diaria vence el mismo día)."""
    import os as _os
    if isinstance(tipo, str):
        tipo = TIPOS_CLAVE_N.get(tipo.lower().strip())
    tipo = int(tipo) if tipo else 0
    if tipo not in TIPOS_CLAVE:
        raise ValueError("tipo de clave invalido: usa semanal, mensual, "
                         "anual, permanente o diaria")
    cuerpo = bytes([1, tipo]) + _os.urandom(4)
    return (CLAVE_PREFIJO + "-"
            + "-".join(_crock_enc(cuerpo + _clave_mac(cuerpo))[i:i + 4]
                       for i in range(0, 16, 4)))


def clave_validar(texto):
    """(ok, motivo, info). motivo: '', 'formato', 'falsificada',
    'desconocida' o 'vencida'. info: {'tipo','dias'}."""
    t = clave_normalizar(texto)
    if not t.startswith(CLAVE_PREFIJO):
        return False, "formato", {}
    cuerpo = t[len(CLAVE_PREFIJO):]
    if len(cuerpo) != 16:
        return False, "formato", {}
    try:
        datos = _crock_dec(cuerpo)
    except (ValueError, OverflowError):
        return False, "formato", {}
    if len(datos) != 10 or datos[0] != 1:
        return False, "formato", {}
    if _clave_mac(datos[:6]) != datos[6:]:
        return False, "falsificada", {}
    tipo = datos[1]
    if tipo not in TIPOS_CLAVE:
        return False, "desconocida", {}
    nombre, dias = TIPOS_CLAVE[tipo]
    return True, "", {"tipo": nombre, "dias": dias}


def _clave_revocada(norm):
    """¿Está la clave en claves_revocadas.txt del repo? True / False /
    None si no se pudo consultar (sin internet)."""
    url = (f"https://raw.githubusercontent.com/{CLAVES_REPO}/main/"
           f"claves_revocadas.txt")
    try:
        texto = _web_http_get(url, timeout=8)
    except Exception:
        return None
    # cuerpo = clave sin el prefijo AP4, para comparar en la misma base
    cuerpo = (norm[len(CLAVE_PREFIJO):]
              if norm.startswith(CLAVE_PREFIJO) else norm)
    for linea in texto.splitlines():
        l = clave_normalizar(linea.split("#")[0])
        if l.startswith(CLAVE_PREFIJO):
            l = l[len(CLAVE_PREFIJO):]
        # prefijo >= 8: revocar un lote sin matar claves de otros tipos
        if len(l) >= 8 and (cuerpo == l or cuerpo.startswith(l)):
            return True
    return False


def _reg_token():
    """PAT del registro (ofuscado xor 0x5A). '' si falta configurar."""
    if not _REG_TOKEN_B64:
        return ""
    import base64
    try:
        return bytes(b ^ 0x5A for b in base64.b64decode(
            _REG_TOKEN_B64.encode("ascii"))).decode("utf-8")
    except Exception:
        return ""


def _reg_contiene(texto, norm):
    """¿La clave normalizada está anotada en el texto del registro?
    Ignora líneas vacías y comentarios (#)."""
    for linea in (texto or "").splitlines():
        cuerpo = clave_normalizar(linea.split("#")[0])
        if cuerpo and cuerpo == norm:
            return True
    return False


def _reg_leer():
    """Lee usadas.txt del repo privado. (texto, '') o (None, motivo)
    si no se pudo leer (sin token o sin internet)."""
    token = _reg_token()
    if not token:
        return None, "sin-token"
    res = _github_api(f"repos/{REGISTRO_REPO}/contents/{REGISTRO_ARCHIVO}",
                      token=token)
    if not isinstance(res, dict) or not isinstance(res.get("content"), str):
        # Un 404 y un fallo de red se ven igual acá: por eso usadas.txt
        # ya viene sembrado en el repo. Si no se pudo leer, no se concede
        # el uso (mejor denegar de más que dejar pasar una clave gastada).
        return None, "sin-internet"
    import base64
    try:
        texto = base64.b64decode(res["content"]).decode("utf-8",
                                                        errors="replace")
    except Exception:
        return None, "error"
    return texto, ""


def _reg_escribir(texto, token):
    """Escribe usadas.txt completo (PUT con sha). 'ok' o 'error'.
    Si el sha quedó viejo (otra PC escribió primero) reintenta una vez."""
    import base64
    ruta = f"repos/{REGISTRO_REPO}/contents/{REGISTRO_ARCHIVO}"
    cuerpo = {"message": "Registro de claves usadas (AutoPiano)",
              "content": base64.b64encode(texto.encode("utf-8")
                                          ).decode("ascii")}
    for _intento in range(2):
        previo = _github_api(ruta, token=token)
        if isinstance(previo, dict) and previo.get("sha"):
            cuerpo["sha"] = previo["sha"]
        res = _github_api(ruta, "PUT", cuerpo, token)
        if isinstance(res, dict):
            return "ok"
        # casi siempre sha viejo: se vuelve a leer y se reintenta
    return "error"


def _reg_agregar(norm):
    """Anota la clave como usada (un solo uso). Devuelve '' si quedó
    anotada, 'usada' si ya estaba gastada o 'sin-internet' si no se
    pudo verificar ni anotar (en ese caso NO se concede el uso)."""
    token = _reg_token()
    if not token:
        return "sin-internet"
    texto, _err = _reg_leer()
    if texto is None:
        return "sin-internet"
    if _reg_contiene(texto, norm):
        return "usada"
    nuevo = texto
    if nuevo and not nuevo.endswith("\n"):
        nuevo += "\n"
    nuevo += norm + "\n"
    if _reg_escribir(nuevo, token) != "ok":
        return "sin-internet"
    return ""


def _reg_quitar(norm):
    """Borra la clave del registro (deshace un fallo posterior al
    anotarla). True si quedó borrada; si falla se deja anotada
    (mejor de más que de menos)."""
    token = _reg_token()
    if not token:
        return False
    texto, _err = _reg_leer()
    if texto is None:
        return False
    nuevas, fuera = [], False
    for linea in texto.splitlines():
        if clave_normalizar(linea.split("#")[0]) == norm:
            fuera = True
            continue
        nuevas.append(linea)
    if not fuera:
        return True
    nuevo = "\n".join(nuevas)
    if nuevo:
        nuevo += "\n"
    return _reg_escribir(nuevo, token) == "ok"


def activar_clave(texto):
    """Valida la clave (firma + revocación + UN SOLO USO por internet,
    una sola vez) y guarda la activación local. Devuelve (ok, motivo).
    Las claves permanentes son exentas: no se registran ni gastan."""
    ok, motivo, info = clave_validar(texto)
    if not ok:
        return False, motivo
    norm = clave_normalizar(texto)
    if _clave_revocada(norm) is True:
        return False, "revocada"
    es_permanente = info["tipo"] == "permanente"
    if not es_permanente:
        estado_reg = _reg_agregar(norm)
        if estado_reg == "usada":
            return False, "usada"
        if estado_reg:
            return False, "sin-internet"
    import datetime
    hoy = datetime.date.today()
    vence = ""
    if info["tipo"] == "diaria":
        vence = hoy.isoformat()       # dura hasta el final de HOY
    elif info["dias"]:
        vence = (hoy + datetime.timedelta(days=info["dias"])).isoformat()
    try:
        _escribe_json(ACTIVACION_FILE, {
            "clave": norm, "tipo": info["tipo"], "dias": info["dias"],
            "activada": hoy.isoformat(), "vence": vence})
    except Exception:
        if not es_permanente:
            _reg_quitar(norm)         # rollback: no la dejo gastada
        return False, "error"
    return True, ""


def _activacion_vigente():
    """(ok, motivo, datos). motivo: '', 'sin-activar' o 'vencida'.
    La clave permanente nunca vence; las demás comparan fecha local
    (sin internet, como pediste: se valida una sola vez)."""
    import datetime
    if not os.path.exists(ACTIVACION_FILE):
        return False, "sin-activar", {}
    try:
        with open(ACTIVACION_FILE, "r", encoding="utf-8-sig") as f:
            datos = json.load(f)
    except Exception:
        return False, "sin-activar", {}
    if not isinstance(datos, dict) or not datos.get("clave"):
        return False, "sin-activar", {}
    vence = str(datos.get("vence") or "")
    if not vence:
        return True, "", datos          # permanente
    try:
        v = datetime.date.fromisoformat(vence)
    except Exception:
        return False, "vencida", datos
    if datetime.date.today() > v:
        return False, "vencida", datos
    return True, "", datos


def _dialogo_activacion(root, motivo=""):
    """Pantalla de activación (bloquea el uso hasta tener clave válida).
    Devuelve True si quedó activada."""
    import threading
    win = tk.Toplevel(root)
    win.title("Activar AutoPiano")
    win.geometry("560x540")
    win.configure(bg="#2b2b2b")
    win.grab_set()
    win.resizable(False, False)

    tk.Label(win, text="🔑 Activar AutoPiano", bg="#2b2b2b", fg="white",
             font=("Segoe UI", 16, "bold")).pack(anchor="w", padx=18,
                                                 pady=(18, 4))
    if motivo == "vencida":
        vence = ""
        try:
            with open(ACTIVACION_FILE, encoding="utf-8-sig") as f:
                vence = json.load(f).get("vence", "")
        except Exception:
            pass
        aviso, color = ((f"Tu clave venció el {vence}. "
                         f"Pegá una nueva para seguir usando la app."
                         if vence else
                         "Tu clave venció. Pegá una nueva para seguir "
                         "usando la app."), "#ff9f6b")
    else:
        aviso, color = ("Esta copia de AutoPiano no tiene una clave "
                        "activa. Necesitás una clave para usarla.", "#ffe066")
    tk.Label(win, text=aviso, bg="#2b2b2b", fg=color,
             font=("Segoe UI", 11), wraplength=520, justify="left"
             ).pack(anchor="w", padx=18)
    tk.Label(win, text="Tipos de clave:  diaria (hoy, gratis viendo 1\n"
                       "anuncio) · semanal (7 días) · mensual (30) ·\n"
                       "anual (365) · permanente (no vence). El reloj\n"
                       "empieza cuando la activás.",
             bg="#2b2b2b", fg="#aaaaaa", font=("Segoe UI", 10),
             justify="left").pack(anchor="w", padx=18, pady=(6, 0))

    fila = tk.Frame(win, bg="#2b2b2b")
    fila.pack(fill="x", padx=18, pady=(14, 0))
    entrada = tk.Entry(fila, font=("Consolas", 13), justify="center")
    entrada.pack(fill="x")
    entrada.insert(0, CLAVE_PREFIJO + "-")
    entrada.select_range(len(CLAVE_PREFIJO) + 1, "end")

    estado = tk.Label(win, text="", bg="#2b2b2b", fg="#ffd7d7",
                      font=("Segoe UI", 10, "bold"), wraplength=520,
                      justify="left")
    estado.pack(anchor="w", padx=18, pady=(10, 0))

    resultado = {"ok": False}
    # anti doble-Enter: si ya hay una validación en vuelo, no arrancar
    # otra (dos workers = la misma clave se registra dos veces y la 2ª
    # responde "usada" contra la clave del propio usuario).
    en_curso = {"n": False}

    def salir():
        win.destroy()

    def activar():
        if en_curso["n"]:
            return                     # Enter repetido: ignorar
        en_curso["n"] = True
        texto = entrada.get()
        btn_act.config(state="disabled")
        btn_regalo.config(state="disabled")
        btn_reclamar.config(state="disabled")
        estado.config(text="⏳ Validando clave…", fg="#ffe066")
        caja = {}                    # el hilo sólo deja el resultado acá

        def worker():
            try:
                caja["res"] = activar_clave(texto)
            except Exception as e:
                caja["res"] = (False, f"error: {e}")

        def done(res):
            en_curso["n"] = False      # libre: se puede reintentar
            if res[0]:
                resultado["ok"] = True
                win.destroy()
                return
            # Si el worker terminó DESPUÉS del timeout de 40 s, la
            # activación pudo haberse guardado igual: en ese caso no
            # decimos "sin respuesta" (y quemaría la clave sin avisar).
            if res[1] == "error: sin respuesta":
                ok_tarde, _m, _d = _activacion_vigente()
                if ok_tarde:
                    resultado["ok"] = True
                    win.destroy()
                    return
            motivos = {
                "formato": "Esa clave no tiene el formato correcto.",
                "falsificada": "Clave incorrecta o alterada.",
                "desconocida": "Tipo de clave desconocido.",
                "revocada": "Esta clave fue revocada por el creador.",
                "usada": ("Esa clave ya fue usada: cada clave sirve una "
                          "sola vez. Pedí una nueva o comprá otra."),
                "sin-internet": ("No se pudo conectar con el registro de "
                                 "claves. Revisá tu internet y probá "
                                 "otra vez."),
                "error": ("No se pudo guardar la activación. "
                          "Cerrá y volvé a intentar."),
            }
            estado.config(
                text=motivos.get(res[1], f"No se pudo activar: {res[1]}"),
                fg="#ffd7d7")
            btn_act.config(state="normal")
            # el botón del anuncio sólo se re-habilita si todavía NO se
            # vio (si ya se vio, el usuario debe reclamar, no ver otro)
            if not regalo.visto:
                btn_regalo.config(state="normal")
            btn_reclamar.config(state="normal")
            entrada.focus_set()
            entrada.select_range(0, "end")

        # OJO: root.after desde el HILO SECUNDARIO revienta con
        # "main thread is not in main loop" mientras el hilo principal
        # está en wait_window (y también ANTES de mainloop, que es
        # justo cómo arranca el candado en main()). Así que el worker
        # sólo escribe en "caja" y el hilo principal la vigila.
        def vigilar(n=0):
            if not win.winfo_exists():
                return
            if "res" in caja:
                done(caja["res"])
            elif n < 400:            # 100 ms x 400 = 40 s (red + registro)
                root.after(100, lambda: vigilar(n + 1))
            else:
                done((False, "error: sin respuesta"))

        threading.Thread(target=worker, daemon=True).start()
        root.after(100, vigilar)

    btns = tk.Frame(win, bg="#2b2b2b")
    btns.pack(fill="x", padx=18, pady=(16, 0))
    btn_act = tk.Button(btns, text="✅ Activar", command=activar,
                        bg="#3a7d44", fg="white", font=("Segoe UI", 12,
                                                        "bold"),
                        relief="flat", padx=14, pady=4)
    btn_act.pack(side="left", expand=True, fill="x", padx=(0, 6))
    tk.Button(btns, text="❌ Salir", command=salir, bg="#555555",
              fg="white", font=("Segoe UI", 12), relief="flat",
              padx=14, pady=4).pack(side="right", expand=True, fill="x",
                                    padx=(6, 0))

    # ---------- 🎁 clave diaria gratis viendo 1 anuncio (v4.25) --------
    regalo_f = tk.Frame(win, bg="#2b2b2b")
    regalo_f.pack(fill="x", padx=18, pady=(14, 0))

    def regalo():
        """Abre el anuncio en el navegador y arranca la cuenta
        regresiva; al terminar aparece el botón para reclamar."""
        if not ANUNCIO_URL:
            estado.config(text="⏳ Próximamente: clave diaria gratis con "
                               "1 anuncio.", fg="#ffe066")
            return
        if regalo.en_curso:
            return                     # doble clic: una sola cuenta regresiva
        regalo.en_curso = True
        try:
            webbrowser.open(ANUNCIO_URL)
        except Exception:
            regalo.en_curso = False
            estado.config(text="No se pudo abrir el anuncio en el "
                               "navegador.", fg="#ffd7d7")
            return
        btn_regalo.config(state="disabled")
        restante = {"n": max(0, int(ANUNCIO_ESPERA))}

        def cuenta():
            if not win.winfo_exists():
                return
            if restante["n"] <= 0:
                # el texto final queda fijo: no puede seguir diciendo
                # "Esperá 1 s" con el botón de reclamar ya visible
                regalo.visto = True    # ya no hay que volver a verlo
                btn_regalo.config(text="✅ Anuncio visto")
                btn_reclamar.pack(fill="x")
                estado.config(text="✅ Listo: reclamá tu clave diaria "
                                   "(vence hoy).", fg="#9fffa0")
                return
            btn_regalo.config(text=f"⏳ Esperá {restante['n']} s para "
                                   f"reclamar…")
            restante["n"] -= 1
            root.after(1000, cuenta)

        cuenta()

    regalo.en_curso = False
    regalo.visto = False

    def reclamar():
        """Genera una clave diaria y la activa (queda anotada como
        usada: un solo uso, vence hoy)."""
        btn_reclamar.config(state="disabled")
        try:
            entrada.delete(0, "end")
            entrada.insert(0, clave_generar("diaria"))
        except Exception as e:
            estado.config(text=f"No se pudo generar la clave: {e}",
                          fg="#ffd7d7")
            btn_reclamar.config(state="normal")
            return
        activar()

    btn_regalo = tk.Button(
        regalo_f, text="🎁 Ver 1 anuncio y usar gratis hoy",
        command=regalo, bg="#8a5cd6", fg="white",
        font=("Segoe UI", 12, "bold"), relief="flat", padx=14, pady=4)
    btn_regalo.pack(fill="x")
    btn_reclamar = tk.Button(
        regalo_f, text="✅ Ya lo vi — reclamar clave diaria",
        command=reclamar, bg="#3a7d44", fg="white",
        font=("Segoe UI", 12, "bold"), relief="flat", padx=14, pady=4)
    # sólo se muestra cuando termina la cuenta regresiva

    entrada.bind("<Return>", lambda _e: activar())
    win.protocol("WM_DELETE_WINDOW", salir)
    entrada.focus_set()
    entrada.select_range(len(CLAVE_PREFIJO) + 1, "end")
    win.wait_window()
    return resultado["ok"]


def _web_buscar(query: str, limite: int = 8):
    """Busca la consulta en DuckDuckGo (versión HTML, sin API ni clave)
    y devuelve una lista de URLs de resultados."""
    import urllib.parse
    q = urllib.parse.quote_plus((query or "").strip())
    if not q:
        return []
    pagina = _web_http_get("https://html.duckduckgo.com/html/?q=" + q)
    urls = []
    # cada resultado tiene <a class="result__a" href="…"> (en cualquier
    # orden de atributos); se recorre el documento en orden para
    # respetar el ranking de los resultados
    for m in re.finditer(r"<a\b[^>]*>", pagina):
        tag = m.group(0)
        if 'class="result__a"' not in tag:
            continue
        hm = re.search(r'href="([^"]+)"', tag)
        if not hm:
            continue
        href = hm.group(1)
        # los links de DDG son redirecciones: //duckduckgo.com/l/?uddg=URL
        if "uddg=" in href:
            try:
                consulta = urllib.parse.parse_qs(
                    urllib.parse.urlsplit(href).query)
                href = consulta.get("uddg", [""])[0]
            except Exception:
                continue
        if href.startswith("http") and href not in urls:
            urls.append(href)
        if len(urls) >= limite:
            break
    return urls


def _html_a_texto(pagina: str) -> str:
    """Convierte HTML en texto plano (sin scripts, estilos ni etiquetas)."""
    pagina = re.sub(r"(?is)<(script|style|noscript|svg)[^>]*>.*?</\1>", " ",
                    pagina)
    pagina = re.sub(r"(?s)<!--.*?-->", " ", pagina)
    pagina = re.sub(r"(?i)<br\s*/?>|</p\s*>|</div\s*>|</li\s*>|</h[1-6]\s*>",
                    "\n", pagina)
    pagina = re.sub(r"<[^>]+>", " ", pagina)
    pagina = _html_unescape(pagina)
    pagina = re.sub(r"[ \t\xa0]+", " ", pagina)
    return re.sub(r"\n\s*\n+", "\n\n", pagina).strip()


def _web_descargar(url: str):
    """Descarga una página de la web y devuelve (título, texto plano)."""
    pagina = _web_http_get(url)
    m = re.search(r"(?is)<title[^>]*>(.*?)</title>", pagina)
    if m:
        titulo = re.sub(r"\s+", " ", _html_unescape(
            re.sub(r"<[^>]+>", " ", m.group(1)))).strip()
    else:
        titulo = ""
    return titulo or url, _html_a_texto(pagina)


def _web_buscar_partituras(query: str, avance=None, limite: int = 8):
    """Busca 'query' en la web y devuelve partituras candidatas:
    [{"title":…, "sheet":…, "url":…}] — solo páginas que contienen texto
    que parsea como partitura. 'avance(txt)' se llama por cada página
    leída (para el rótulo de estado, desde cualquier hilo)."""
    res = []
    urls = _web_buscar(query, limite)
    for i, url in enumerate(urls, 1):
        if avance:
            avance(f"⏳ Leyendo {i}/{len(urls)}: {url[:55]}")
        try:
            titulo, texto = _web_descargar(url)
        except Exception:
            continue                      # página caída: sigue con la otra
        for cand in _extract_candidates(texto)[:3]:
            if parse_sheet(cand):
                res.append({"title": titulo, "sheet": cand.strip(),
                            "url": url})
                break
        if len(res) >= limite:
            break
    return res


def _posicion_mouse():
    """Posición actual del cursor en coordenadas de pantalla (x, y);
    None si no se puede consultar."""
    try:
        import ctypes

        class _P(ctypes.Structure):
            _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]

        p = _P()
        if ctypes.windll.user32.GetCursorPos(ctypes.byref(p)):
            return p.x, p.y
    except Exception:
        pass
    return None


class AutoPianoApp:
    VERSION = "4.28"   # bump al hacer cambios: se ve en el título de la ventana

    def __init__(self, root: tk.Tk):
        self.root = root
        root.title(f"AutoPiano Roblox  ·  v{self.VERSION}")
        root.geometry("960x640")
        root.minsize(860, 620)   # debajo de esto se recortarían opciones
        root.configure(bg="#2b2b2b")
        try:
            self._icono_img = self._icono_piano()   # referencia viva
            root.iconphoto(False, self._icono_img)
        except Exception:
            pass        # sin icono propio no pasa nada grave

        self.key_ctrl = KeyController() if PYNPUT_OK else None

        # --- estado de reproducción --------------------------------------
        self.groups = []
        self.pos = 0
        self.playing = False
        self.paused = False
        self.stop_flag = False
        self._compacto = None     # ventana de 📌 modo compacto (si está abierta)
        self._compacto_lista = None   # listbox de canciones de la barra
        self._compacto_vel_lbl = None # rótulo de velocidad de la barra
        self._compacto_rect = None    # posición/tamaño de la barra (x, y, w, h)
        self._compacto_oculta = False  # ¿está escondida por el 👻 fantasma?
        self._compacto_sin_transmision = False  # ¿Windows la excluye de
        #                                         capturas de pantalla?
        self._dirty = False
        self._held = {}        # TECLA FÍSICA presionada -> timer de auto-liberación
        self._shift_timer = None   # timer que suelta el toque de Shift
        self._shift_down = False   # el Shift está presionado ahora mismo
        # --- v4.23: tramo A→B para repetir la parte difícil -------------
        self._marca_a = None       # índice del grupo donde empieza el tramo
        self._marca_b = None       # índice del grupo donde termina
        # --- v4.23: récords por canción y racha de días ----------------
        self.records = {}          # {cancion: {tocadas, mejor_vel}}

        # --- variables de control ----------------------------------------
        self.speed_var = tk.DoubleVar(value=1.0)
        self.hold_var = tk.IntVar(value=120)
        self.realism_var = tk.DoubleVar(value=40.0)
        self.loop_var = tk.BooleanVar(value=False)
        self.rotate_var = tk.BooleanVar(value=False)
        self.practice_var = tk.BooleanVar(value=False)
        self.startcursor_var = tk.BooleanVar(value=False)
        self.search_var = tk.StringVar()
        self.seccion_filter_var = tk.StringVar(value="Todas")   # filtro por sección
        self._practice_keys = set()   # teclas que el usuario mantiene (práctica)
        self._practice_listener = None
        self.speed = 1.0
        self.hold_ms = 120
        self.realism = 0.40
        self._autosave_id = None
        self._settings_save_id = None
        self._cerrando = False     # True al cerrar: los after() de fondo paran
        self._actualizando = False  # True mientras descarga/reemplaza versión

        def _sync_speed(*_):
            try:
                self.speed = max(float(self.speed_var.get()), 0.1)
            except (ValueError, tk.TclError):
                pass

        def _sync_hold(*_):
            try:
                self.hold_ms = max(int(self.hold_var.get()), 10)
            except (ValueError, tk.TclError):
                pass

        def _sync_realism(*_):
            try:
                self.realism = min(max(float(self.realism_var.get()),
                                       0.0), 100.0) / 100.0
            except (ValueError, tk.TclError):
                pass

        self.speed_var.trace_add("write", _sync_speed)
        self.hold_var.trace_add("write", _sync_hold)
        self.realism_var.trace_add("write", _sync_realism)
        # cualquier cambio de control se guarda solo en el archivo de ajustes
        for v in (self.speed_var, self.hold_var, self.realism_var):
            v.trace_add("write", self._persist_settings_from_vars)

        # --- configuración persistente -------------------------------------
        self.settings = self._load_settings()
        self._song_overrides = self._cargar_song_settings()
        self._aplicando_song = False   # aplicando config de una canción
        self._songsave_id = None
        self.base_gap = float(self.settings["base_gap"])
        self.countdown = int(self.settings["countdown"])
        self.long_chance = float(self.settings["long_note_pct"]) / 100.0
        self.breathe_chance = float(self.settings["breathe_pct"]) / 100.0
        # las repeticiones SIEMPRE se re-presionan (fijo, sin casilla:
        # la casilla vieja hacía que las notas repetidas se saltaran)
        self.retrigger_repeats = True
        self.loop_repeats = bool(self.settings.get("loop", False))
        self.loop_var.set(self.loop_repeats)
        self.loop_var.trace_add("write", self._on_loop_toggle)
        self.rotate_songs = bool(self.settings.get("rotate_loop", False))
        self.rotate_var.set(self.rotate_songs)
        self.rotate_var.trace_add("write", self._on_rotate_toggle)
        # orden de la lista de partituras + cuál suena ahora (para rotar)
        self._score_order = []
        self._score_actual = None
        self._cambio_event = threading.Event()
        self.practice_mode = bool(self.settings.get("practice_mode", False))
        self.practice_var.set(self.practice_mode)
        self.practice_var.trace_add("write", self._on_practice_toggle)
        self.start_at_cursor = bool(self.settings.get("start_cursor", False))
        self.startcursor_var.set(self.start_at_cursor)
        self.startcursor_var.trace_add("write", self._on_startcursor_toggle)

        self.scores = self._load_scores()
        self._cargar_secciones()     # secciones (carpetas) de canciones
        self._cargar_colores()       # paleta de colores personalizada
        self._cargar_records()       # v4.23: récords y racha
        self._build_ui()
        # si es una instalación/actualización en carpeta nueva, ofrecer
        # importar las partituras de una versión anterior (con su config)
        self._importar_datos_previos()
        # canciones COMPARTIDAS que vienen junto a la app (se agregan a la
        # lista sin tocar las que el usuario ya tenga)
        self._importar_compartidas()
        # autocurado: overrides de canciones que ya no existen (borradas o
        # renombradas con versiones anteriores) no sirven y se descartan
        huerfanos = [k for k in self._song_overrides if k not in self.scores]
        if huerfanos:
            for k in huerfanos:
                del self._song_overrides[k]
            self._guardar_song_settings()
        # ídem asignaciones de sección de canciones que ya no existen
        h_asig = [k for k in self.seccion_de if k not in self.scores]
        if h_asig:
            for k in h_asig:
                del self.seccion_de[k]
            self._guardar_secciones()
        self._apply_settings()
        self._refresh_list()
        # --- restaurar la última sesión ------------------------------------
        # primero intenta recuperar la partitura que estabas editando; si era
        # una sin guardar (pizarrón nuevo), recupera lo escrito en el pizarrón
        ultimo = self.settings.get("last_score", "")
        if ultimo in self.scores:
            self._score_actual = ultimo
            self._refresh_list(keep=ultimo)   # respeta el filtro de sección
            self._set_board_text(self.scores[ultimo])
            if not self.listbox.curselection():
                # quedó fuera del filtro activo: mostrar la primera visible
                self._refresh_list()
                if self.listbox.size():
                    self.listbox.selection_set(0)
                    self.listbox.activate(0)
                    name = self._current_score_name()
                    if name:
                        self._score_actual = name
                        self._set_board_text(self.scores[name])
        elif self.settings.get("last_board", ""):
            self._set_board_text(self.settings["last_board"])
        elif self.scores:
            self.listbox.selection_set(0)
            self.listbox.activate(0)
            name = self._current_score_name()
            if name:
                self._score_actual = name
                self._set_board_text(self.scores[name])
        # config personalizada de la canción restaurada (si tiene)
        self._aplicar_song_overrides()
        # velocidad en vivo: + / - durante la reproducción
        for seq in ("<plus>", "<minus>", "<KP_Add>", "<KP_Subtract>"):
            self.root.bind(seq, self._speed_hotkey)
        # aplicar la paleta de colores personalizada y barrer de vez en
        # cuando (así los diálogos que se abren después también quedan
        # con los colores del usuario)
        self._colores_aplicados = dict(self.colores)
        self._aplicar_colores()
        # si el arcoíris quedó activado de la sesión anterior, retoma
        if self._rainbow_estado.get("activado"):
            self._rainbow_iniciar()
        self.root.after(1200, self._barrido_colores)
        self._start_hotkey_listener()
        root.protocol("WM_DELETE_WINDOW", self._on_close)

        # aviso de versión nueva: si el archivo cambia en el disco mientras
        # la app está abierta, recordar pulsar ♻ Reiniciar
        try:
            self._script_mtime = os.path.getmtime(os.path.abspath(__file__))
        except OSError:
            self._script_mtime = 0
        root.after(5000, self._check_script_update)

        # aviso automático de versión nueva en internet (GitHub): busca
        # cada tanto y pregunta si actualizar — sin pasar archivos a mano
        threading.Thread(target=self._chequeo_internet_hilo,
                         daemon=True).start()

    # ======================================================================
    # Interfaz
    # ======================================================================
    @staticmethod
    def _icono_piano():
        """Icono de la ventana (32x32): un piano dibujado con píxeles de Tk.
        Sin archivos externos ni dependencias — sirve también portable/exe."""
        img = tk.PhotoImage(width=32, height=32)

        def rect(color, x0, y0, x1, y1):
            img.put(color, to=(x0, y0, x1, y1))

        # placa azul oscura + borde azul claro
        rect("#1e2438", 0, 0, 32, 32)
        for x in range(32):                     # marco
            rect("#78aaff", x, 0, x + 1, 2)
            rect("#78aaff", x, 30, x + 1, 32)
            rect("#78aaff", 0, x, 2, x + 1)
            rect("#78aaff", 30, x, 32, x + 1)
        # marco del teclado
        rect("#0e101a", 3, 7, 29, 26)
        # teclas blancas
        rect("#eef0f6", 4, 8, 28, 25)
        # teclas negras (entre C-D, D-E, F-G, G-A, A-B)
        for cx in (7, 11, 18, 22, 25):
            rect("#121216", cx, 8, cx + 2, 17)
        # separadores de teclas blancas
        for cx in (8, 12, 16, 20, 24):
            rect("#9aa0b4", cx, 17, cx + 1, 25)
        return img

    def _build_ui(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure("TButton", padding=6)

        # ---------- panel izquierdo: lista de partituras ------------------
        left = tk.Frame(self.root, bg="#2b2b2b")
        left.pack(side="left", fill="y", padx=8, pady=8)

        tk.Label(left, text="🎵 Partituras", bg="#2b2b2b", fg="#ffffff",
                 font=("Segoe UI", 13, "bold")).pack(anchor="w", pady=(0, 4))

        tk.Label(left, text="🔎 Buscar:", bg="#2b2b2b", fg="#aaaaaa",
                 font=("Segoe UI", 9)).pack(anchor="w")
        search = tk.Entry(left, textvariable=self.search_var, bg="#1e1e1e",
                          fg="#e8e8e8", insertbackground="#ffe066",
                          font=("Segoe UI", 9), relief="flat",
                          highlightthickness=1, highlightbackground="#444444")
        search.pack(fill="x", pady=(2, 4))
        search.bind("<KeyRelease>", lambda e: self._refresh_list(keep=None))

        # filtro por sección (carpeta) de canciones
        self._sec_row = tk.Frame(left, bg="#2b2b2b")
        self._sec_row.pack(fill="x", pady=(0, 4))
        tk.Label(self._sec_row, text="📂 Ver:", bg="#2b2b2b", fg="#aaaaaa",
                 font=("Segoe UI", 9)).pack(side="left")
        self.combo_seccion = ttk.Combobox(
            self._sec_row, textvariable=self.seccion_filter_var, state="readonly",
            width=15, font=("Segoe UI", 9))
        self._refrescar_combo_secciones()
        self.combo_seccion.pack(side="left", fill="x", expand=True, padx=(4, 0))
        self.combo_seccion.bind("<<ComboboxSelected>>",
                                lambda e: self._refresh_list())

        # barra de carpeta abierta (aparece solo cuando filtrás por sección)
        self.bar_seccion = tk.Frame(left, bg="#6b4a2b")
        self.lbl_bar_seccion = tk.Label(self.bar_seccion, text="", bg="#6b4a2b",
                                        fg="#ffe9c9",
                                        font=("Segoe UI", 10, "bold"))
        self.lbl_bar_seccion.pack(side="left", fill="x", expand=True,
                                  padx=(8, 0), pady=3)
        tk.Button(self.bar_seccion, text="✖ Cerrar carpeta",
                  command=self._cerrar_carpeta, bg="#8b3a3a", fg="white",
                  relief="flat", font=("Segoe UI", 9, "bold"), padx=6
                  ).pack(side="right", padx=4, pady=3)

        self.listbox = tk.Listbox(left, width=21, height=8, bg="#1e1e1e",
                                  fg="#e8e8e8", selectbackground="#4a6da7",
                                  font=("Segoe UI", 10), activestyle="none",
                                  selectmode="extended",   # Ctrl/Shift: varias
                                  exportselection=False)   # que otras listas
        self.listbox.pack(fill="both", expand=True)   # no le borren la selección
        self.listbox.bind("<<ListboxSelect>>", self._on_select_score)
        self.listbox.bind("<Button-3>", self._menu_lista)   # clic derecho
        # tecla M: mover las canciones seleccionadas a una carpeta
        self.listbox.bind("<KeyPress-m>", self._mover_con_tecla)
        # arrastrar canciones seleccionadas hasta el filtro "📂 Ver:"
        self.listbox.bind("<ButtonPress-1>", self._dnd_press)
        self.listbox.bind("<B1-Motion>", self._dnd_motion)
        self.listbox.bind("<ButtonRelease-1>", self._dnd_release)

        btns = tk.Frame(left, bg="#2b2b2b")
        btns.pack(fill="x", pady=6)
        tk.Button(btns, text="🎥 Analizar video", command=self._analyze_video_dialog,
                  bg="#3a5a7d", fg="white", relief="flat", padx=8,
                  font=("Segoe UI", 10, "bold")).pack(fill="x", pady=2)
        tk.Button(btns, text="🌐 Buscar notas en la web",
                  command=self._buscar_notas_dialog,
                  bg="#2f6b5a", fg="white", relief="flat", padx=8,
                  font=("Segoe UI", 10, "bold")).pack(fill="x", pady=2)
        tk.Button(btns, text="📈 Récords", command=self._records_dialog,
                  bg="#6b4a2b", fg="white", relief="flat", padx=8,
                  font=("Segoe UI", 10, "bold")).pack(fill="x", pady=2)
        tk.Button(btns, text="🌍 Comunidad", command=self._comunidad_dialog,
                  bg="#2f5a6b", fg="white", relief="flat", padx=8,
                  font=("Segoe UI", 10, "bold")).pack(fill="x", pady=2)
        tk.Button(btns, text="☁️ Mi nube", command=self._nube_dialog,
                  bg="#4a4a8a", fg="white", relief="flat", padx=8,
                  font=("Segoe UI", 10, "bold")).pack(fill="x", pady=2)
        tk.Button(btns, text="📤 Exportar a .txt", command=self._export_txt,
                  bg="#555555", fg="white", relief="flat").pack(fill="x", pady=2)
        tk.Button(btns, text="💾 Respaldo total", command=self._backup_all,
                  bg="#4a4a8a", fg="white", relief="flat").pack(fill="x", pady=2)
        tk.Button(btns, text="📥 Restaurar respaldo", command=self._restore_backup,
                  bg="#4a4a8a", fg="white", relief="flat").pack(fill="x", pady=2)
        tk.Button(btns, text="🗑 Eliminar", command=self._delete_score,
                  bg="#8b3a3a", fg="white", relief="flat").pack(fill="x", pady=2)
        tk.Button(btns, text="📂 Secciones…", command=self._dialogo_secciones,
                  bg="#6b4a2b", fg="white", relief="flat").pack(fill="x", pady=2)
        tk.Button(btns, text="🎨 Colores", command=self._dialogo_colores,
                  bg="#3a3a6d", fg="white", relief="flat").pack(fill="x", pady=2)
        tk.Button(btns, text="📌 Modo compacto", command=self._compacto_abrir,
                  bg="#2f5a4e", fg="white", relief="flat").pack(fill="x", pady=2)

        # ---------- panel central: pizarrón interactivo --------------------
        center = tk.Frame(self.root, bg="#8b5a2b")
        center.pack(side="left", fill="both", expand=True, padx=8, pady=8)

        toolbar_wrap = tk.Frame(center, bg="#8b5a2b")
        toolbar_wrap.pack(fill="x", pady=(0, 5))
        toolbar = tk.Frame(toolbar_wrap, bg="#8b5a2b")
        toolbar.pack(fill="x")
        self._tb_row1 = toolbar
        self._tb_row2 = tk.Frame(toolbar_wrap, bg="#8b5a2b")   # 2ª fila (se
        tbtn = dict(relief="flat", bg="#5f3f1e", fg="#ffe9c9",  # muestra solo
                    font=("Segoe UI", 9, "bold"), padx=7, pady=2)  # si falta
        # los botones van a una fila sola si entran; si no, se reparten en
        # dos filas (así nunca desaparecen aunque la ventana esté chica)
        # master común (toolbar_wrap) para poder repartir con pack(in_=…)
        self._tb_botones = [
            tk.Button(toolbar_wrap, text="💾 Guardar", command=self._save_board, **tbtn),
            tk.Button(toolbar_wrap, text="✏ Nueva", command=self._new_board, **tbtn),
            tk.Button(toolbar_wrap, text="🔁 Renombrar", command=self._rename_score, **tbtn),
            tk.Button(toolbar_wrap, text="⧉ Duplicar", command=self._duplicate_score, **tbtn),
            tk.Button(toolbar_wrap, text="⬆ Octava",
                      command=lambda: self._transpose_board(1), **tbtn),
            tk.Button(toolbar_wrap, text="⬇ Octava",
                      command=lambda: self._transpose_board(-1), **tbtn),
            tk.Button(toolbar_wrap, text="🧹 Limpiar", command=self._clean_board, **tbtn),
        ]
        for b in self._tb_botones:
            b.pack(in_=toolbar, side="left", padx=4)
        self.lbl_boardinfo = tk.Label(toolbar_wrap, text="Notas: 0   Acordes: 0",
                                      bg="#8b5a2b", fg="#ffe9c9",
                                      font=("Segoe UI", 9, "bold"))
        self.lbl_boardinfo.pack(in_=toolbar, side="right")
        toolbar.bind("<Configure>",
                     lambda e: self.root.after_idle(self._ajustar_toolbar))

        board_wrap = tk.Frame(center, bg="#274e36", bd=6, relief="groove",
                              highlightthickness=4,
                              highlightbackground="#8b5a2b")
        board_wrap.pack(fill="both", expand=True)

        tk.Label(board_wrap, text="PIZARRÓN  (escribe aquí con el teclado)",
                 bg="#274e36", fg="#c9b98a",
                 font=("Georgia", 9, "italic")).pack(pady=(3, 0))

        board_area = tk.Frame(board_wrap, bg="#274e36")
        board_area.pack(fill="both", expand=True, padx=6, pady=4)

        self.board = tk.Text(board_area, bg="#274e36", fg="#f7f3e3",
                             font=("Consolas", 13, "bold"), wrap="word",
                             state="normal", undo=True, bd=0,
                             highlightthickness=0, spacing3=4, padx=6, pady=3,
                             insertbackground="#ffe066")
        scroll = ttk.Scrollbar(board_area, command=self.board.yview)
        self.board.config(yscrollcommand=scroll.set)
        scroll.pack(side="right", fill="y")
        self.board.pack(side="left", fill="both", expand=True)

        self.board.tag_configure("hl", background="#ffe066", foreground="#1a1a1a")
        self.board.bind("<KeyRelease>", self._on_board_key)
        self.board.bind("<Control-s>", lambda e: (self._save_board(), "break")[1])
        self.board.focus_set()

        self.lbl_progreso = tk.Label(center, text="—", bg="#8b5a2b", fg="#ffe9c9",
                                     font=("Segoe UI", 9))
        self.lbl_progreso.pack(pady=(2, 0))
        self.progreso = ttk.Progressbar(center, mode="determinate", maximum=1,
                                        length=300, value=0)
        self.progreso.pack(fill="x", padx=20, pady=(1, 4))

        # ---------- panel derecho: controles + guía (con scroll) -----------
        outer = tk.Frame(self.root, bg="#2b2b2b", width=250)
        outer.pack(side="right", fill="y", padx=8, pady=8)
        outer.pack_propagate(False)

        canvas = tk.Canvas(outer, bg="#2b2b2b", highlightthickness=0)
        vsb = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)

        inner = tk.Frame(canvas, bg="#2b2b2b")
        inner_id = canvas.create_window((0, 0), window=inner, anchor="nw")
        inner.bind("<Configure>",
                   lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>",
                    lambda e: canvas.itemconfigure(inner_id, width=e.width))

        tk.Label(inner, text="⚙ Controles", bg="#2b2b2b", fg="#ffffff",
                 font=("Segoe UI", 12, "bold")).pack(anchor="w", pady=(0, 4))

        tk.Button(inner, text="⚙ Ajustes avanzados (se guardan)",
                  command=self._settings_dialog, bg="#4a4a8a", fg="white",
                  relief="flat", font=("Segoe UI", 10, "bold"), pady=5
                  ).pack(fill="x", pady=(0, 4))
        tk.Button(inner, text="♻ Reiniciar app (cargar cambios)",
                  command=self._restart_app, bg="#555555", fg="white",
                  relief="flat", font=("Segoe UI", 9), pady=4
                  ).pack(fill="x", pady=(0, 10))

        # casillas numéricas: escribes el valor y SE GUARDA SOLO
        def ctrl_row(label, var, lo, hi, step, is_int):
            tk.Label(inner, text=label, bg="#2b2b2b", fg="#cccccc",
                     font=("Segoe UI", 10)).pack(anchor="w")
            sp = tk.Spinbox(inner, from_=lo, to=hi, increment=step,
                            textvariable=var, width=9,
                            font=("Segoe UI", 11, "bold"),
                            background="#1e1e1e", foreground="#7ec8ff",
                            buttonbackground="#333333",
                            insertbackground="#ffe066",
                            highlightthickness=1,
                            highlightbackground="#444444",
                            relief="flat")
            sp.pack(anchor="w", pady=(0, 8))

            def validar(_e=None):
                try:
                    v = float(sp.get())
                except (ValueError, tk.TclError):
                    return
                if is_int:
                    v = int(round(v))
                else:
                    v = round(v, 2)
                var.set(min(max(v, lo), hi))

            sp.bind("<Return>", validar)
            sp.bind("<FocusOut>", validar)

            def rueda(e):
                paso = step if e.delta > 0 else -step
                try:
                    var.set(min(max(float(var.get()) + paso, lo), hi))
                except (ValueError, tk.TclError):
                    pass
                return "break"

            sp.bind("<MouseWheel>", rueda)
            return sp

        ctrl_row("Velocidad (0.1 a 20)", self.speed_var, 0.1, 20, 0.1, False)
        ctrl_row("Tecla mantenida en ms (10 a 5000)", self.hold_var,
                 10, 5000, 10, True)
        ctrl_row("Realismo en % (0 a 100)", self.realism_var, 0, 100, 5, False)

        tk.Label(inner, text="⬦ Las repeticiones SIEMPRE se re-presionan:"
                             " si una tecla vuelve a salir mientras sigue"
                             " presionada, se suelta y se vuelve a tocar"
                             " (la repetición se escucha).",
                 bg="#2b2b2b", fg="#777777", font=("Segoe UI", 8),
                 wraplength=230, justify="left"
                 ).pack(anchor="w", pady=(0, 10))

        tk.Checkbutton(
            inner, text="🔁 Repetir en bucle",
            variable=self.loop_var, bg="#2b2b2b", fg="#cccccc",
            activebackground="#2b2b2b", activeforeground="#7ec8ff",
            selectcolor="#1e1e1e", font=("Segoe UI", 9),
            anchor="w").pack(anchor="w")
        tk.Label(inner, text="⬦ la canción se repite sola al terminar "
                             "(2 s entre vueltas). Detén con F7.",
                 bg="#2b2b2b", fg="#777777", font=("Segoe UI", 8),
                 wraplength=230, justify="left"
                 ).pack(anchor="w")

        tk.Checkbutton(
            inner, text="🎵 Bucle rotando canciones",
            variable=self.rotate_var, bg="#2b2b2b", fg="#cccccc",
            activebackground="#2b2b2b", activeforeground="#7ec8ff",
            selectcolor="#1e1e1e", font=("Segoe UI", 9),
            anchor="w").pack(anchor="w")
        tk.Label(inner, text="⬦ al terminar cada vuelta pasa a la "
                             "SIGUIENTE partitura de la lista, y al "
                             "acabar la última vuelve a la primera "
                             "(activa el bucle solo).",
                 bg="#2b2b2b", fg="#777777", font=("Segoe UI", 8),
                 wraplength=230, justify="left"
                 ).pack(anchor="w", pady=(0, 10))

        tk.Checkbutton(
            inner, text="🎹 Modo práctica (yo toco)",
            variable=self.practice_var, bg="#2b2b2b", fg="#cccccc",
            activebackground="#2b2b2b", activeforeground="#7ec8ff",
            selectcolor="#1e1e1e", font=("Segoe UI", 9),
            anchor="w").pack(anchor="w")
        tk.Label(inner, text="⬦ la app NO toca: espera a que presiones TÚ la"
                             " nota correcta (Roblox la sonará). Pasa a la"
                             " siguiente cuando sueltes.",
                 bg="#2b2b2b", fg="#777777", font=("Segoe UI", 8),
                 wraplength=230, justify="left"
                 ).pack(anchor="w", pady=(0, 10))

        tk.Checkbutton(
            inner, text="📍 Iniciar desde el cursor",
            variable=self.startcursor_var, bg="#2b2b2b", fg="#cccccc",
            activebackground="#2b2b2b", activeforeground="#7ec8ff",
            selectcolor="#1e1e1e", font=("Segoe UI", 9),
            anchor="w").pack(anchor="w")
        tk.Label(inner, text="⬦ haz clic en una nota del pizarrón y la"
                             " canción empieza ahí (para ensayar partes).",
                 bg="#2b2b2b", fg="#777777", font=("Segoe UI", 8),
                 wraplength=230, justify="left"
                 ).pack(anchor="w", pady=(0, 10))

        self.btn_play = tk.Button(inner, text="▶  Iniciar  (F8)",
                                  command=self.start_play,
                                  bg="#3a7d44", fg="white",
                                  font=("Segoe UI", 10, "bold"),
                                  relief="flat", pady=5)
        self.btn_play.pack(fill="x", pady=2)

        self.btn_pause = tk.Button(inner, text="⏸  Pausar  (F6)",
                                   command=self.toggle_pause,
                                   bg="#b8860b", fg="white",
                                   font=("Segoe UI", 10, "bold"),
                                   relief="flat", pady=5, state="disabled")
        self.btn_pause.pack(fill="x", pady=2)

        self.btn_stop = tk.Button(inner, text="⏹  Detener  (F7)",
                                  command=self.stop_play,
                                  bg="#8b3a3a", fg="white",
                                  font=("Segoe UI", 10, "bold"),
                                  relief="flat", pady=5, state="disabled")
        self.btn_stop.pack(fill="x", pady=2)

        # --- v4.23: tramo A→B (repetir la parte difícil) ---------------
        marcos = tk.Frame(inner, bg="#2b2b2b")
        marcos.pack(fill="x", pady=(6, 2))
        self.btn_marca_a = tk.Button(
            marcos, text="📍A", command=lambda: self._marcar_tramo("A"),
            bg="#3d5a80", fg="white", font=("Segoe UI", 9, "bold"),
            relief="flat", padx=6, pady=3)
        self.btn_marca_a.pack(side="left", expand=True, fill="x",
                              padx=(0, 2))
        self.btn_marca_b = tk.Button(
            marcos, text="📍B", command=lambda: self._marcar_tramo("B"),
            bg="#3d5a80", fg="white", font=("Segoe UI", 9, "bold"),
            relief="flat", padx=6, pady=3)
        self.btn_marca_b.pack(side="left", expand=True, fill="x",
                              padx=(0, 2))
        self.btn_marca_x = tk.Button(
            marcos, text="✖", command=self._limpiar_tramo,
            bg="#555555", fg="white", font=("Segoe UI", 9, "bold"),
            relief="flat", padx=8, pady=3)
        self.btn_marca_x.pack(side="left")
        self.lbl_tramo = tk.Label(inner, text="Tramo: —", bg="#2b2b2b",
                                  fg="#888888", font=("Segoe UI", 9))
        self.lbl_tramo.pack(anchor="w")
        tk.Label(inner, text="📍A empieza / 📍B termina: la canción repite\n"
                             "ese tramo en bucle hasta que aprietes ✖ o ⏹.",
                 bg="#2b2b2b", fg="#777777", font=("Segoe UI", 8),
                 wraplength=230, justify="left").pack(anchor="w")

        self.lbl_estado = tk.Label(inner, text="Listo", bg="#2b2b2b", fg="#9fe870",
                                   font=("Segoe UI", 10, "bold"), wraplength=220)
        self.lbl_estado.pack(pady=12)

        tk.Label(inner, justify="left", bg="#2b2b2b", fg="#aaaaaa",
                 font=("Segoe UI", 9),
                 text="Atajos globales (funcionan aunque Roblox\n"
                      "esté en primer plano):\n"
                      "F8  →  Iniciar\n"
                      "F6  →  Pausar / Continuar\n"
                      "F7  →  Detener").pack(anchor="w", pady=(8, 0))

        tk.Label(inner, text="📖 Funciones de los botones", bg="#2b2b2b",
                 fg="#ffffff", font=("Segoe UI", 12, "bold")
                 ).pack(anchor="w", pady=(18, 4))

        tk.Label(inner, text=LEGENDA, justify="left", bg="#1e1e1e", fg="#d9cfae",
                 font=("Segoe UI", 8), wraplength=250, padx=8, pady=8
                 ).pack(fill="x")

        if not PYNPUT_OK:
            tk.Label(inner, text="⚠ Falta 'pynput'.\nEjecuta:\npip install pynput",
                     bg="#5a1f1f", fg="#ffd7d7", justify="center",
                     font=("Segoe UI", 10, "bold")).pack(fill="x", pady=(16, 0))

        self._bind_wheel(outer, canvas)

    # ======================================================================
    # Rueda del mouse para el panel derecho
    # ======================================================================
    def _bind_wheel(self, container, canvas):
        def on_wheel(ev):
            n = -ev.delta / 120.0
            if n and abs(n) < 1:
                n = math.copysign(1.0, n)
            canvas.yview_scroll(int(n), "units")

        def hook(_e):
            canvas.bind_all("<MouseWheel>", on_wheel)

        def unhook(_e):
            canvas.unbind_all("<MouseWheel>")

        def rec(w):
            w.bind("<Enter>", hook)
            w.bind("<Leave>", unhook)
            for c in w.winfo_children():
                rec(c)

        rec(container)

    # ======================================================================
    # Partituras: carga, guardado, lista
    # ======================================================================
    def _load_scores(self):
        if os.path.exists(SCORES_FILE):
            try:
                # utf-8-sig: tolera archivos guardados con BOM (Bloc de notas…)
                with open(SCORES_FILE, "r", encoding="utf-8-sig") as f:
                    return json.load(f)
            except Exception:
                # archivo dañado (corte de luz, cierre forzado…): respaldarlo
                # para poder recuperarlo a mano y no perderlo para siempre
                try:
                    shutil.copyfile(SCORES_FILE, SCORES_FILE + ".corrupto-"
                                    + time.strftime("%Y%m%d-%H%M%S"))
                except Exception:
                    pass
        return dict(DEFAULT_SCORES)

    def _save_scores(self):
        try:
            _escribe_json(SCORES_FILE, self.scores)
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo guardar:\n{e}")

    def _importar_datos_previos(self):
        """ACTUALIZACIONES: si esta carpeta no tiene partituras todavía pero
        en el PC hay una instalación anterior de AutoPiano (Escritorio,
        Documentos, Descargas…), ofrece traer sus partituras AQUÍ junto con
        su configuración global y la personalizada de cada canción. Así una
        versión nueva no parte de cero nunca."""
        if os.path.exists(SCORES_FILE):
            return                      # ya tiene datos: nada que hacer
        if self.settings.get("importar_preguntado", False):
            return                      # ya se preguntó antes: no insistir
        nombre_scores = os.path.basename(SCORES_FILE)
        candidatas = []
        for d in _directorios_datos():
            try:
                p = os.path.join(d, nombre_scores)
                if os.path.isfile(p):
                    candidatas.append(p)
            except OSError:
                pass
        candidatas.sort(key=os.path.getmtime, reverse=True)
        for p in candidatas:
            try:
                with open(p, "r", encoding="utf-8-sig") as f:
                    data = json.load(f)
            except Exception:
                continue
            if not (isinstance(data, dict) and data):
                continue
            carpeta = os.path.dirname(p)
            n = len(data)
            if not messagebox.askyesno(
                    "AutoPiano",
                    f"Se encontraron {n} partitura(s) de otra versión de "
                    f"AutoPiano en:\n{carpeta}\n\n"
                    "¿Importarlas AQUÍ junto con sus configuraciones\n"
                    "(velocidad por canción, ajustes, bucle…)?",
                    parent=self.root):
                break                   # no importar; no volver a preguntar
            try:
                shutil.copyfile(p, SCORES_FILE)
                for nombre in (os.path.basename(SETTINGS_FILE),
                               os.path.basename(SONG_SETTINGS_FILE)):
                    src = os.path.join(carpeta, nombre)
                    if os.path.isfile(src):
                        shutil.copyfile(src,
                                        os.path.join(_APP_DIR, nombre))
            except Exception:
                continue
            # recargar todo en memoria desde los archivos recién copiados
            try:
                self.scores = self._load_scores()
                self.settings = self._load_settings()
                self._song_overrides = self._cargar_song_settings()
            except Exception:
                pass
            self._refresh_list()
            self._ui(self.lbl_estado.config,
                     text=f"📥 Importadas {n} partituras con su configuración")
            return
        # sin candidato válido (o usuario dijo no): marcar para no insistir
        self.settings["importar_preguntado"] = True
        self._save_settings_quiet()

    # ======================================================================
    # Ajustes avanzados (persistentes)
    # ======================================================================
    def _load_settings(self):
        if os.path.exists(SETTINGS_FILE):
            try:
                # utf-8-sig: tolera archivos guardados con BOM (Bloc de notas…)
                with open(SETTINGS_FILE, "r", encoding="utf-8-sig") as f:
                    data = json.load(f)
                merged = dict(DEFAULT_SETTINGS)
                merged.update({k: v for k, v in data.items() if k in merged})
                return merged
            except Exception:
                # respaldar el archivo dañado (no perderlo)
                try:
                    shutil.copyfile(SETTINGS_FILE, SETTINGS_FILE + ".corrupto-"
                                    + time.strftime("%Y%m%d-%H%M%S"))
                except Exception:
                    pass
        return dict(DEFAULT_SETTINGS)

    def _cargar_song_settings(self):
        """Configuración personalizada POR CANCIÓN: {nombre: {speed, ...}}"""
        if os.path.exists(SONG_SETTINGS_FILE):
            try:
                with open(SONG_SETTINGS_FILE, "r", encoding="utf-8-sig") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    return {k: dict(v) for k, v in data.items()
                            if isinstance(v, dict)}
            except Exception:
                try:
                    shutil.copyfile(SONG_SETTINGS_FILE, SONG_SETTINGS_FILE
                                    + ".corrupto-" + time.strftime("%Y%m%d-%H%M%S"))
                except Exception:
                    pass
        return {}

    def _guardar_song_settings(self):
        self._songsave_id = None
        try:
            _escribe_json(SONG_SETTINGS_FILE, self._song_overrides)
        except Exception:
            pass

    def _aplicar_song_overrides(self, name=None):
        """Aplica la configuración PERSONALIZADA de la canción seleccionada
        (si tiene) o la global. Solo cambia los controles: no escribe
        ajustes ni overrides (está blindado con _aplicando_song)."""
        self._aplicando_song = True
        try:
            name = name or getattr(self, "_score_actual", None)
            ov = self._song_overrides.get(name, {}) if name else {}
            for var, key, cast in (
                    (self.speed_var, "speed", float),
                    (self.hold_var, "hold_ms", int),
                    (self.realism_var, "realism", float)):
                try:
                    var.set(cast(ov.get(key, self.settings[key])))
                except (KeyError, ValueError, tk.TclError):
                    pass
            try:
                self.base_gap = float(ov.get("base_gap",
                                             self.settings["base_gap"]))
            except (KeyError, ValueError):
                pass
        finally:
            self._aplicando_song = False

    def _importar_compartidas(self):
        """CANCIONES COMPARTIDAS: si junto al programa viene un archivo
        autopiano_compartidas.json (el que acompaña a la app compartida),
        lo FUSIONA con lo que ya hay: agrega a la lista las partituras que
        falten, con su configuración por canción, SIN tocar ni cambiar
        ninguna canción que el usuario ya tenga guardada (si una que llega
        se llama igual, se agrega como 'nombre (compartida)'). Al terminar
        renombra el archivo para no volver a fusionarlo."""
        if not os.path.isfile(COMPARTIDAS_FILE):
            return
        try:
            with open(COMPARTIDAS_FILE, "r", encoding="utf-8-sig") as f:
                data = json.load(f)
        except Exception:
            try:
                os.replace(COMPARTIDAS_FILE, COMPARTIDAS_FILE + ".daniado")
            except OSError:
                pass
            return
        if not isinstance(data, dict):
            return
        nuevos = data.get("scores")
        cfgs = data.get("song_settings")
        nuevos = nuevos if isinstance(nuevos, dict) else {}
        cfgs = cfgs if isinstance(cfgs, dict) else {}
        # CARPETAS que viajan con el compartido (opcional; archivos viejos
        # no la tienen y caen al comportamiento de antes)
        secs_in = []
        asig_in = {}
        bloque = data.get("secciones")
        if isinstance(bloque, dict):
            lista = bloque.get("secciones")
            if isinstance(lista, list):
                for s in lista:
                    if (isinstance(s, str) and s.strip()
                            and s.strip() != "General"
                            and s.strip() not in secs_in):
                        secs_in.append(s.strip())
            a = bloque.get("asignaciones")
            if isinstance(a, dict):
                asig_in = {k: v.strip() for k, v in a.items()
                           if isinstance(k, str) and isinstance(v, str)
                           and v.strip()}
        cambios = 0
        llegan = []
        for nombre, cuerpo in nuevos.items():
            if not (isinstance(nombre, str) and isinstance(cuerpo, str)):
                continue
            destino = nombre
            if nombre in self.scores:
                if self.scores[nombre] == cuerpo:
                    continue        # idéntica: nada que agregar
                destino = f"{nombre} (compartida)"
                i = 2
                while destino in self.scores:
                    destino = f"{nombre} (compartida {i})"
                    i += 1
            self.scores[destino] = cuerpo
            if isinstance(cfgs.get(nombre), dict):
                self._song_overrides[destino] = dict(cfgs[nombre])
            llegan.append((destino, nombre))
            cambios += 1
        if cambios:
            if secs_in:
                # recrear las carpetas de quien comparte, SIN borrar las
                # que el receptor ya tenga (los nombres iguales se unen)
                for s in secs_in:
                    if s not in self.secciones:
                        self.secciones.append(s)
                for destino, original in llegan:
                    sec = asig_in.get(original)
                    self.seccion_de[destino] = (
                        sec if sec in self.secciones else "General")
            else:
                # sin info de carpetas: todas a SU propia sección
                # "Compartidas", separadas de las que el usuario ya tenía
                if "Compartidas" not in self.secciones:
                    self.secciones.append("Compartidas")
                for destino, _original in llegan:
                    self.seccion_de[destino] = "Compartidas"
            self._save_scores()
            self._guardar_song_settings()
            self._guardar_secciones()
            self._refrescar_combo_secciones()
            self._refresh_list()
            detalle = ("con sus carpetas" if secs_in
                       else "sección Compartidas")
            self._ui(self.lbl_estado.config,
                     text=f"🎁 Agregadas {cambios} canciones compartidas "
                          f"({detalle})")
        try:
            os.replace(COMPARTIDAS_FILE, COMPARTIDAS_FILE + ".procesado")
        except OSError:
            pass

    def _save_settings(self):
        try:
            _escribe_json(SETTINGS_FILE, self.settings)
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo guardar la configuración:\n{e}")

    def _persist_settings_from_vars(self, *_):
        """Cada vez que cambian velocidad/tecla/realismo (spinbox, +/- o ⚙):
        - con una partitura seleccionada, el cambio va SOLO a SU
          configuración personalizada (lo global queda intacto, así la
          config de una canción no se contagia a la siguiente)
        - sin partitura (pizarrón libre), el cambio es el global
        """
        if getattr(self, "_aplicando_song", False):
            return          # aplicando la config de otra canción: no escribir
        try:
            speed = round(float(self.speed_var.get()), 2)
        except (ValueError, tk.TclError):
            return
        try:
            hold = int(float(self.hold_var.get()))
        except (ValueError, tk.TclError):
            hold = None
        try:
            real = round(float(self.realism_var.get()), 1)
        except (ValueError, tk.TclError):
            real = None
        name = getattr(self, "_score_actual", None)
        if name and name in self.scores:
            # SOLO la config de esta canción: la global no se toca
            ov = self._song_overrides.setdefault(name, {})
            ov["speed"] = speed
            if hold is not None:
                ov["hold_ms"] = hold
            if real is not None:
                ov["realism"] = real
            if self._songsave_id:
                self.root.after_cancel(self._songsave_id)
            self._songsave_id = self.root.after(800, self._guardar_song_settings)
            return
        # sin canción seleccionada: cambio global
        self.settings["speed"] = speed
        if hold is not None:
            self.settings["hold_ms"] = hold
        if real is not None:
            self.settings["realism"] = real
        # guardado diferido (evita escribir el disco en cada tecla)
        if self._settings_save_id:
            self.root.after_cancel(self._settings_save_id)
        self._settings_save_id = self.root.after(800, self._save_settings_quiet)

    def _save_settings_quiet(self):
        self._settings_save_id = None
        try:
            _escribe_json(SETTINGS_FILE, self.settings)
        except Exception:
            pass

    def _on_loop_toggle(self, *_):
        """Casilla 'Repetir en bucle': se guarda automáticamente."""
        self.loop_repeats = bool(self.loop_var.get())
        self.settings["loop"] = self.loop_repeats
        # sin bucle no tiene sentido rotar: apagar también la rotación
        if not self.loop_repeats and self.rotate_songs:
            self.rotate_var.set(False)
        self._save_settings_quiet()

    def _on_rotate_toggle(self, *_):
        """Casilla 'Bucle rotando canciones': se guarda automáticamente.
        Rotar implica bucle: al activarla se activa el bucle."""
        self.rotate_songs = bool(self.rotate_var.get())
        self.settings["rotate_loop"] = self.rotate_songs
        if self.rotate_songs and not self.loop_repeats:
            self.loop_var.set(True)
        self._save_settings_quiet()

    def _on_practice_toggle(self, *_):
        self.practice_mode = bool(self.practice_var.get())
        self.settings["practice_mode"] = self.practice_mode
        self._save_settings_quiet()

    def _on_startcursor_toggle(self, *_):
        self.start_at_cursor = bool(self.startcursor_var.get())
        self.settings["start_cursor"] = self.start_at_cursor
        self._save_settings_quiet()

    def _apply_settings(self):
        s = self.settings
        # blindado: aplicar la config GLOBAL no debe escribir overrides
        # de canción ni contaminar la config de la canción seleccionada
        self._aplicando_song = True
        try:
            self.speed_var.set(float(s["speed"]))
            self.hold_var.set(int(s["hold_ms"]))
            self.realism_var.set(float(s["realism"]))
        finally:
            self._aplicando_song = False
        self.base_gap = float(s["base_gap"])
        self.countdown = int(s["countdown"])
        self.long_chance = float(s["long_note_pct"]) / 100.0
        self.breathe_chance = float(s["breathe_pct"]) / 100.0
        # retrigger fijo en True (sin casilla); limpiar la clave vieja
        self.retrigger_repeats = True
        self.settings.pop("retrigger_repeats", None)
        self.loop_repeats = bool(s.get("loop", False))
        if self.loop_var.get() != self.loop_repeats:
            self.loop_var.set(self.loop_repeats)
        self.rotate_songs = bool(s.get("rotate_loop", False))
        if self.rotate_var.get() != self.rotate_songs:
            self.rotate_var.set(self.rotate_songs)
        self.practice_mode = bool(s.get("practice_mode", False))
        if self.practice_var.get() != self.practice_mode:
            self.practice_var.set(self.practice_mode)
        self.start_at_cursor = bool(s.get("start_cursor", False))
        if self.startcursor_var.get() != self.start_at_cursor:
            self.startcursor_var.set(self.start_at_cursor)
        self.board.config(font=("Consolas", int(s["board_font"]), "bold"))

    def _settings_dialog(self):
        fields = [
            ("Velocidad (x)", "speed", float, 0.1, 20),
            ("Tecla mantenida (ms)", "hold_ms", int, 10, 5000),
            ("Realismo (% de variación)", "realism", float, 0, 100),
            ("Separación base entre notas (seg)", "base_gap", float, 0.05, 5),
            ("Cuenta regresiva antes de tocar (seg)", "countdown", int, 0, 10),
            ("% de notas largas (efecto pedal)", "long_note_pct", float, 0, 100),
            ("% de pausas de respiración", "breathe_pct", float, 0, 100),
            ("Tamaño de letra del pizarrón", "board_font", int, 8, 30),
        ]
        win = tk.Toplevel(self.root)
        win.title("⚙ Ajustes avanzados")
        win.geometry("460x440")
        win.configure(bg="#2b2b2b")
        win.grab_set()

        tk.Label(win, text="⚙ Ajustes avanzados", bg="#2b2b2b", fg="white",
                 font=("Segoe UI", 13, "bold")).pack(anchor="w", padx=14,
                                                     pady=(12, 2))
        tk.Label(win, text="Escribe el valor que quieras. Todo se guarda y "
                           "queda igual la próxima vez que abras la app.\n"
                           "Con una partitura seleccionada, la velocidad, el "
                           "sostenido y el realismo se guardan como SU "
                           "configuración personalizada (no tocan a las "
                           "otras canciones). Sin partitura seleccionada, "
                           "son los valores globales.",
                 bg="#2b2b2b", fg="#aaaaaa", font=("Segoe UI", 9),
                 wraplength=420, justify="left").pack(anchor="w", padx=14,
                                                      pady=(0, 8))
        # los valores que muestra el diálogo son los EFECTIVOS: los de la
        # canción seleccionada si tiene config propia, y la global si no
        name_eff = getattr(self, "_score_actual", None)
        ov_eff = self._song_overrides.get(name_eff, {}) if name_eff else {}
        eff = {k: (ov_eff[k] if k in ov_eff else self.settings[k])
               for k, *_ in fields}
        entries = {}
        for label, key, kind, lo, hi in fields:
            row = tk.Frame(win, bg="#2b2b2b")
            row.pack(fill="x", padx=14, pady=3)
            tk.Label(row, text=label, bg="#2b2b2b", fg="#cccccc",
                     font=("Segoe UI", 10), width=32, anchor="w"
                     ).pack(side="left")
            e = tk.Entry(row, width=10, font=("Consolas", 11))
            e.pack(side="right")
            e.insert(0, f"{eff[key]:g}")
            entries[key] = (e, kind, lo, hi)

        def guardar():
            valores = {}
            for key, (e, kind, lo, hi) in entries.items():
                raw = e.get().strip().replace(",", ".")
                try:
                    val = kind(raw)
                except ValueError:
                    messagebox.showwarning("AutoPiano",
                                           f"Valor inválido para:\n{key}",
                                           parent=win)
                    return
                valores[key] = min(max(val, lo), hi)
            tempo = {"speed", "hold_ms", "realism", "base_gap"}
            name = getattr(self, "_score_actual", None)
            if name and name in self.scores:
                # con canción seleccionada: velocidad/hold/realismo/separación
                # van a SU config; lo demás (cuenta regresiva, pedal,
                # respiración, letra) es global y no se toca el tempo global
                ov = self._song_overrides.setdefault(name, {})
                for key in tempo:
                    ov[key] = valores[key]
                for key, val in valores.items():
                    if key not in tempo:
                        self.settings[key] = val
                self._guardar_song_settings()
                self._save_settings_quiet()
                # aplicar en vivo: tempo desde la config de la canción
                self._aplicando_song = True
                try:
                    self.speed_var.set(float(ov["speed"]))
                    self.hold_var.set(int(ov["hold_ms"]))
                    self.realism_var.set(float(ov["realism"]))
                finally:
                    self._aplicando_song = False
                self.base_gap = float(ov["base_gap"])
                self.countdown = int(self.settings["countdown"])
                self.long_chance = float(self.settings["long_note_pct"]) / 100.0
                self.breathe_chance = float(self.settings["breathe_pct"]) / 100.0
                self.board.config(font=("Consolas",
                                        int(self.settings["board_font"]), "bold"))
            else:
                # sin canción: todo es global
                for key, val in valores.items():
                    self.settings[key] = val
                self._save_settings()
                self._apply_settings()
            self.lbl_estado.config(text="⚙ Ajustes guardados y aplicados")
            win.destroy()

        def restablecer():
            self.settings = dict(DEFAULT_SETTINGS)
            self._save_settings()
            self._apply_settings()
            # borrar la configuración personalizada de la canción actual
            name = getattr(self, "_score_actual", None)
            if name and name in self._song_overrides:
                del self._song_overrides[name]
                self._guardar_song_settings()
            # re-mostrar los valores efectivos (ahora todos globales)
            ov_nuevo = self._song_overrides.get(name, {}) if name else {}
            for key, (e, _kind, _lo, _hi) in entries.items():
                val = ov_nuevo.get(key, self.settings[key])
                e.delete(0, "end")
                e.insert(0, f"{val:g}")
            self.lbl_estado.config(text="⚙ Ajustes restablecidos")

        row2 = tk.Frame(win, bg="#2b2b2b")
        row2.pack(fill="x", padx=14, pady=10)
        tk.Button(row2, text="💾 Guardar y aplicar", command=guardar,
                  bg="#3a7d44", fg="white", relief="flat",
                  font=("Segoe UI", 11, "bold")).pack(side="right")
        tk.Button(row2, text="↺ Restablecer", command=restablecer,
                  bg="#555555", fg="white", relief="flat").pack(side="right",
                                                                padx=6)
        tk.Button(row2, text="Cerrar", command=win.destroy,
                  bg="#777777", fg="white", relief="flat").pack(side="right",
                                                                padx=6)

    def _refresh_list(self, keep=None):
        # orden ALFABÉTICO automático (para el bucle rotativo y para ver)
        self._score_order = sorted(self.scores.keys(), key=str.lower)
        filtro = ""
        try:
            filtro = self.search_var.get().strip().lower()
        except (AttributeError, tk.TclError):
            pass
        seccion = "Todas"
        try:
            seccion = self.seccion_filter_var.get() or "Todas"
        except (AttributeError, tk.TclError):
            pass
        self.listbox.delete(0, "end")
        visibles = [n for n in self._score_order
                    if (not filtro or filtro in n.lower())
                    and (seccion == "Todas"
                         or self.seccion_de.get(n, "General") == seccion)]
        for name in visibles:
            self.listbox.insert("end", name)
        if keep and keep in self.scores and keep in visibles:
            idx = visibles.index(keep)
            self.listbox.selection_clear(0, "end")
            self.listbox.selection_set(idx)
            self.listbox.activate(idx)
        self._refrescar_barra_seccion()
        self._compacto_refrescar_lista()   # espejar en el modo compacto

    def _refrescar_barra_seccion(self):
        """Muestra/oculta la barra de carpeta abierta con su botón
        '✖ Cerrar carpeta' (para volver a ver la lista completa)."""
        try:
            sec = self.seccion_filter_var.get()
        except (AttributeError, tk.TclError):
            return
        if sec and sec != "Todas":
            n = sum(1 for k in self.scores
                    if self.seccion_de.get(k, "General") == sec)
            self.lbl_bar_seccion.config(text=f"📂 {sec}   ({n} canciones)")
            try:
                self.bar_seccion.pack(fill="x", pady=(0, 4),
                                      before=self.listbox)
            except tk.TclError:
                pass
        else:
            self.bar_seccion.pack_forget()

    def _cerrar_carpeta(self):
        """Vuelve a 'Todas': se ve la lista completa de canciones."""
        self.seccion_filter_var.set("Todas")
        self._refresh_list()
        self.lbl_estado.config(
            text="📂 Carpeta cerrada — mostrando todas las canciones")

    def _current_score_name(self):
        sel = self.listbox.curselection()
        if not sel:
            return None
        # con multi-selección (Ctrl/Shift), la canción activa es la
        # clickeada (la "active" de la lista), no la primera elegida
        try:
            act = self.listbox.index("active")
        except tk.TclError:
            act = -1
        if act in sel:
            return self.listbox.get(act)
        return self.listbox.get(sel[0])

    def _on_select_score(self, _evt=None):
        name = self._current_score_name()
        if not name:
            return
        if self.playing:
            self.stop_play()
        self._score_actual = name
        self._limpiar_tramo_al_cambiar()   # v4.23: el tramo era de la otra
        self._set_board_text(self.scores[name])
        # config personalizada de ESTA canción (si tiene)
        self._aplicar_song_overrides(name)
        self._compacto_sincronizar()   # refleja la elección en la barra

    # ======================================================================
    # Pizarrón interactivo
    # ======================================================================
    def _clear_group_tags(self):
        names = [t for t in self.board.tag_names() if t.startswith("g")]
        if names:
            self.board.tag_delete(*names)
        self.board.tag_remove("hl", "1.0", "end")

    def _set_board_text(self, text):
        if self._autosave_id:
            self.root.after_cancel(self._autosave_id)
            self._autosave_id = None
        self.board.config(state="normal")
        self.board.delete("1.0", "end")
        self.board.insert("1.0", text)
        self._clear_group_tags()
        self._dirty = False
        self._refresh_boardinfo()
        self._update_progress()

    def _on_board_key(self, _evt=None):
        if self.playing:
            return
        self._dirty = True
        self._refresh_boardinfo()
        self._schedule_autosave()

    def _schedule_autosave(self):
        """Auto-guarda la edición en la partitura seleccionada tras 1.5 s
        sin escribir (no pierdes cambios si cambias de partitura o cierras)."""
        if self._autosave_id:
            self.root.after_cancel(self._autosave_id)
        self._autosave_id = self.root.after(1500, self._autosave_board)

    def _autosave_board(self):
        self._autosave_id = None
        if self.playing or not self._dirty:
            return
        name = self._current_score_name()
        if not name:
            return            # partitura nueva sin nombre → usa 💾 Guardar
        body = self.board.get("1.0", "end-1c").strip()
        if not body:
            return            # pizarrón vacío: no borramos la partitura
        self.scores[name] = body
        self._save_scores()
        self._dirty = False
        self._refresh_boardinfo()

    def _refresh_boardinfo(self):
        g = parse_sheet(self.board.get("1.0", "end-1c"))
        notas = sum(1 for x in g if x != ["-"])
        pausas = sum(1 for x in g if x == ["-"])
        chords = sum(1 for x in g if len(x) > 1)
        txt = f"Notas: {notas}   Acordes: {chords}   Pausas: {pausas}"
        # duración estimada: grupos x separación / velocidad (+ cuenta regresiva)
        if g:
            secs = len(g) * (self.base_gap / max(self.speed, 0.1))
            m, s = divmod(int(round(secs)) + self.countdown, 60)
            txt += f"   ⏱ ~{m}:{s:02d}"
        if self._dirty:
            txt += "   ● sin guardar"
        self.lbl_boardinfo.config(text=txt)

    def _tag_groups(self, text):
        """Crea tags g0, g1, ... sobre el texto del pizarrón para resaltar.
        Usa el MISMO tokenizador que parse_sheet, así lo resaltado es
        exactamente lo que se toca (incluye las reglas de delimitadores
        sin cerrar)."""
        self._clear_group_tags()
        self.groups = []
        for inicio, fin, grupo in _tokenize_sheet(text):
            self.board.tag_add(f"g{len(self.groups)}",
                               f"1.0+{inicio}c", f"1.0+{fin}c")
            self.groups.append(grupo)

    def _highlight(self, idx):
        self.board.tag_remove("hl", "1.0", "end")
        if self.groups and 0 <= idx < len(self.groups):
            self.board.tag_add("hl", f"g{idx}.first", f"g{idx}.last")
            self.board.see(f"g{idx}.first")

    def _update_progress(self):
        total = len(self.groups)
        self.progreso.config(maximum=max(total, 1), value=min(self.pos, total))
        if total:
            self.lbl_progreso.config(text=f"Nota {min(self.pos + 1, total)} de {total}"
                                          f"   ({self.pos * 100 // total}%)")
        else:
            self.lbl_progreso.config(text="—")

    # ======================================================================
    # Botones del pizarrón: guardar / nueva / renombrar
    # ======================================================================
    def _save_board(self):
        if self.playing:
            return
        body = self.board.get("1.0", "end-1c").strip()
        if not body:
            messagebox.showinfo("AutoPiano", "El pizarrón está vacío.")
            return
        name = self._current_score_name()
        if name is None:
            name = simpledialog.askstring("Guardar partitura",
                                          "Nombre de la partitura:",
                                          parent=self.root)
            if not name:
                return
            name = name.strip()
        es_nueva = name not in self.scores
        self.scores[name] = body
        self._score_actual = name      # ya es la canción activa (config va a ELLA)
        if es_nueva:
            self._asignar_seccion_nueva(name)
        self._save_scores()
        self._refresh_list(keep=name)
        self._dirty = False
        self._refresh_boardinfo()
        self.lbl_estado.config(text=f"💾 '{name}' guardada")

    def _new_board(self):
        if self.playing:
            self.stop_play()
        self.listbox.selection_clear(0, "end")
        # pizarrón libre: los cambios de config pasan a ser GLOBALES
        self._score_actual = None
        self._aplicar_song_overrides()
        self._set_board_text("")
        self.board.focus_set()
        self.lbl_estado.config(text="✏ Escribe la partitura nueva…")

    def _duplicate_score(self):
        """Crea una copia de la partitura seleccionada (por si quieres
        probar variaciones sin perder la original)."""
        name = self._current_score_name()
        if not name:
            messagebox.showinfo("AutoPiano",
                                "Selecciona una partitura de la lista para duplicar.")
            return
        base = f"{name} (copia)"
        nuevo, i = base, 2
        while nuevo in self.scores:
            nuevo = f"{base} {i}"
            i += 1
        self.scores[nuevo] = self.scores[name]
        # la copia nace con la MISMA configuración que la original
        if name in self._song_overrides:
            self._song_overrides[nuevo] = dict(self._song_overrides[name])
            self._guardar_song_settings()
        # y en la MISMA sección
        if name in self.seccion_de:
            self.seccion_de[nuevo] = self.seccion_de[name]
            self._guardar_secciones()
        self._save_scores()
        self._refresh_list(keep=nuevo)
        self.lbl_estado.config(text=f"⧉ Duplicada como '{nuevo}'")

    def _transpose_board(self, direction):
        """Sube (1) o baja (-1) la octava de las notas simples del pizarrón
        agregando o quitando '!' delante de cada letra minúscula. Las notas
        dentro de ( )/[ ] y las teclas de piano completo (números,
        mayúsculas, ^) no se tocan."""
        if self.playing:
            return
        text = self.board.get("1.0", "end-1c")
        # proteger rangos de acordes ( ... ) y [ ... ]
        protegido = [False] * len(text)
        i = 0
        while i < len(text):
            if text[i] in "([":
                cierre = ")" if text[i] == "(" else "]"
                j = text.find(cierre, i + 1)
                j = len(text) - 1 if j == -1 else j
                for k in range(i, j + 1):
                    protegido[k] = True
                i = j + 1
            else:
                i += 1
        out = []
        cambios = 0
        i = 0
        while i < len(text):
            c = text[i]
            sig = text[i + 1] if i + 1 < len(text) else ""
            if c == "!" and not protegido[i]:
                if direction < 0 and sig.islower() and sig.isalpha():
                    out.append(sig)      # quita el '!' y CONSERVA la letra
                    cambios += 1
                    i += 2
                    continue
                out.append(c)
                i += 1
                continue
            if (c.islower() and c.isalpha() and not protegido[i]
                    and direction > 0):
                if i > 0 and text[i - 1] == "!":
                    out.append(c)        # ya tiene '!': no duplicar
                    i += 1
                    continue
                out.append("!")
                cambios += 1
            out.append(c)
            i += 1
        if not cambios:
            messagebox.showinfo(
                "AutoPiano",
                "No hay notas de octava para cambiar ahí.\n\n"
                "⬆ agrega '!' a las letras (subir octava);\n"
                "⬇ lo quita (bajar octava).\n"
                "Las notas dentro de ( )/[ ] no se tocan.")
            return
        self._set_board_text("".join(out))
        self._on_board_key()
        self.lbl_estado.config(
            text=("⬆ Octava subida" if direction > 0 else "⬇ Octava bajada")
                 + f" ({cambios} notas)")

    def _clean_board(self):
        """Quita símbolos basura de texto pegado (|, *, comas, etc.) y
        compacta los espacios. Conserva notas, acordes y pausas."""
        if self.playing:
            return
        text = self.board.get("1.0", "end-1c")
        import re as _re
        limpio = _re.sub(r"[^\w\^\!\(\)\[\]\-\s]", " ", text)
        limpio = _re.sub(r"[ \t]+", " ", limpio)
        limpio = "\n".join(l.strip() for l in limpio.splitlines()
                           if l.strip())
        self._set_board_text(limpio)
        self._on_board_key()
        self.lbl_estado.config(text="🧹 Pizarrón limpiado")

    def _rename_score(self):
        name = self._current_score_name()
        if not name:
            messagebox.showinfo("AutoPiano",
                                "Selecciona una partitura de la lista para renombrar.")
            return
        new = simpledialog.askstring("Renombrar", "Nuevo nombre:",
                                     initialvalue=name, parent=self.root)
        if not new or new.strip() == name:
            return
        new = new.strip()
        if new in self.scores:
            messagebox.showwarning("AutoPiano", "Ya existe una partitura con ese nombre.")
            return
        self.scores = {(new if k == name else k): v for k, v in self.scores.items()}
        # la configuración personalizada SIGUE a la canción al renombrar
        if name in self._song_overrides:
            self._song_overrides[new] = self._song_overrides.pop(name)
            self._guardar_song_settings()
        # la sección (carpeta) también sigue a la canción
        if name in self.seccion_de:
            self.seccion_de[new] = self.seccion_de.pop(name)
            self._guardar_secciones()
        if getattr(self, "_score_actual", None) == name:
            self._score_actual = new
        self._save_scores()
        self._refresh_list(keep=new)
        self.lbl_estado.config(text=f"🔁 Renombrada a '{new}'")

    # ======================================================================
    # Secciones (carpetas de canciones): agrupar, mover, filtrar
    # ======================================================================
    def _ajustar_toolbar(self):
        """Reparte los botones del pizarrón en 1 o 2 filas según el ancho
        disponible: así NINGUNO desaparece cuando la ventana está chica."""
        try:
            if self._cerrando:
                return
            avail = self._tb_botones[0].master.winfo_width()
        except (IndexError, tk.TclError, AttributeError):
            return
        if avail <= 1:      # todavía no se dibuja la ventana
            return
        try:
            ancho_info = self.lbl_boardinfo.winfo_reqwidth()
        except tk.TclError:
            ancho_info = 0
        anchos = [b.winfo_reqwidth() + 8 for b in self._tb_botones]
        total = sum(anchos) + ancho_info + 16
        if total <= avail:
            # entra en una fila: todo arriba, 2ª fila oculta
            for b in self._tb_botones:
                b.pack_forget()
                b.pack(in_=self._tb_row1, side="left", padx=4)
            self._tb_row2.pack_forget()
            self.lbl_boardinfo.pack_forget()
            self.lbl_boardinfo.pack(in_=self._tb_row1, side="right")
            return
        # no entra: repartir en dos filas equilibradas
        mitad = avail / 2.0
        acum = 0
        corte = 0
        for i, a in enumerate(anchos):
            acum += a
            if acum >= mitad:
                corte = i + 1
                break
        else:
            corte = max(1, len(anchos) - 1)
        for i, b in enumerate(self._tb_botones):
            b.pack_forget()
            b.pack(in_=(self._tb_row1 if i < corte else self._tb_row2),
                   side="left", padx=4)
        self._tb_row2.pack(fill="x", pady=(0, 5), after=self._tb_row1)
        self.lbl_boardinfo.pack_forget()
        self.lbl_boardinfo.pack(in_=self._tb_row2, side="right")

    def _cargar_secciones(self):
        """Carga autopiano_secciones.json: {secciones: [...], asignaciones:
        {cancion: seccion}}. 'General' siempre existe; una canción sin
        asignación cae en General."""
        self.secciones = ["General"]
        self.seccion_de = {}
        if os.path.exists(SECCIONES_FILE):
            try:
                with open(SECCIONES_FILE, "r", encoding="utf-8-sig") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    secs = data.get("secciones")
                    if isinstance(secs, list):
                        vistas = ["General"]
                        for s in secs:
                            if (isinstance(s, str) and s.strip()
                                    and s.strip() not in vistas):
                                vistas.append(s.strip())
                        self.secciones = vistas
                    asig = data.get("asignaciones")
                    if isinstance(asig, dict):
                        self.seccion_de = {
                            k: v for k, v in asig.items()
                            if isinstance(k, str) and isinstance(v, str)
                            and v in self.secciones}
            except Exception:
                pass    # archivo dañado: arrancamos con solo General

    def _guardar_secciones(self):
        try:
            _escribe_json(SECCIONES_FILE, {
                "secciones": self.secciones,
                "asignaciones": dict(self.seccion_de)})
        except Exception:
            pass

    # ==================================================================
    # Colores personalizados de la interfaz
    # ==================================================================
    @staticmethod
    def _hex_valido(s):
        return bool(re.fullmatch(r"#[0-9a-fA-F]{6}", s or ""))

    @staticmethod
    def _hex_a_rgb(s):
        """'#rrggbb' -> (r, g, b) 0..255."""
        s = (s or "").strip()
        if not AutoPianoApp._hex_valido(s):
            return (0, 0, 0)
        return (int(s[1:3], 16), int(s[3:5], 16), int(s[5:7], 16))

    @staticmethod
    def _rgb_a_hex(r, g, b):
        return f"#{int(r):02x}{int(g):02x}{int(b):02x}"

    def _cargar_colores(self):
        """Carga autopiano_colores.json sobre la paleta por defecto.
        Valores inválidos o claves desconocidas se ignoran."""
        self.colores = dict(COLORES_DEFAULT)
        self._colores_aplicados = dict(COLORES_DEFAULT)
        self._rainbow_estado = {"activado": False, "ola": True,
                                "velocidad": 3}
        if not hasattr(self, "_colores_historial"):
            self._colores_historial = {}    # hex ya pintados -> clave
        if os.path.exists(COLORES_FILE):
            try:
                with open(COLORES_FILE, "r", encoding="utf-8-sig") as f:
                    data = json.load(f)
                gua = data.get("colores") if isinstance(data, dict) else None
                if isinstance(gua, dict):
                    for k, v in gua.items():
                        if k in COLORES_DEFAULT and self._hex_valido(str(v)):
                            self.colores[k] = str(v).lower()
                rb = data.get("rainbow") if isinstance(data, dict) else None
                if isinstance(rb, dict):
                    if isinstance(rb.get("activado"), bool):
                        self._rainbow_estado["activado"] = rb["activado"]
                    if isinstance(rb.get("ola"), bool):
                        self._rainbow_estado["ola"] = rb["ola"]
                    try:
                        v = int(rb.get("velocidad"))
                        if 1 <= v <= 10:
                            self._rainbow_estado["velocidad"] = v
                    except (TypeError, ValueError):
                        pass
            except Exception:
                pass    # archivo dañado: paleta por defecto

    def _guardar_colores(self):
        try:
            _escribe_json(COLORES_FILE, {
                "colores": dict(self.colores),
                "rainbow": dict(self._rainbow_estado)})
        except Exception:
            pass

    def _mapa_colores(self):
        """Color actual/por defecto -> clave de la paleta. Incluye los
        valores YA aplicados antes (si el usuario cambia un color, los
        widgets que aún tienen el viejo se actualizan igual)."""
        mapa = {v: k for k, v in COLORES_DEFAULT.items()}
        for k, v in self._colores_aplicados.items():
            mapa.setdefault(v, k)
        return mapa

    def _aplicar_colores(self):
        """Recorre TODOS los widgets y repinta los que usen algún color
        de la paleta (fondo, texto y selección de listas)."""
        mapa = self._mapa_colores()
        # el historial recuerda TODOS los hex que cada clave tuvo en esta
        # sesión: si un widget quedó pintado con un valor viejo (paleta
        # recargada, respaldo restaurado…), igual se le llega a actualizar
        mapa.update(getattr(self, "_colores_historial", {}))
        for k, v in self._colores_aplicados.items():
            mapa.setdefault(v, k)

        def rec(w):
            for h in w.winfo_children():
                rec(h)
            # las franjas del borde arcoíris se pintan solas: no tocarlas
            if any(w is m for m in getattr(self, "_marco_bordes", [])):
                return
            try:
                bg = str(w.cget("bg"))
            except (tk.TclError, KeyError):
                bg = ""
            try:
                fg = str(w.cget("fg"))
            except (tk.TclError, KeyError):
                fg = ""
            try:
                if bg in mapa:
                    w.configure(bg=self.colores[mapa[bg]])
            except tk.TclError:
                pass
            try:
                if fg in mapa:
                    w.configure(fg=self.colores[mapa[fg]])
            except tk.TclError:
                pass
            if isinstance(w, tk.Listbox):
                try:
                    sb = str(w.cget("selectbackground"))
                    if sb in mapa:
                        w.configure(
                            selectbackground=self.colores[mapa[sb]])
                except tk.TclError:
                    pass

        try:
            rec(self.root)
        except tk.TclError:
            pass
        self._colores_aplicados = dict(self.colores)
        for k, v in self.colores.items():
            self._colores_historial[v] = k
        # el arcoíris genera muchísimos hex por sesión: si el historial
        # crece demasiado se limpia (los valores viejos ya no interesan)
        if len(self._colores_historial) > 512:
            self._colores_historial.clear()

    def _barrido_colores(self):
        """Barrido periódico: los diálogos que se abren después nacen
        con los colores por defecto; acá se les aplica la paleta."""
        self._aplicar_colores()
        try:
            self.root.after(1200, self._barrido_colores)
        except tk.TclError:
            pass

    # ==================================================================
    # Modo arcoíris 🌈 (solo bordes)
    # ==================================================================
    def _marco_arcoiris_colocar(self):
        """Crea (una vez) y muestra las 4 franjas del borde de la
        ventana: es lo único que pinta el modo arcoíris, así el resto
        de la interfaz conserva la paleta del usuario."""
        if not getattr(self, "_marco_bordes", None):
            g = 5     # grosor de la franja
            self._marco_bordes = [
                tk.Frame(self.root, bg="#888888", bd=0,
                         highlightthickness=0)
                for _ in range(4)]
        top, izq, der, abajo = self._marco_bordes
        try:
            top.place(x=0, y=0, relwidth=1.0, height=g, anchor="nw")
            izq.place(x=0, y=0, relheight=1.0, width=g, anchor="nw")
            der.place(relx=1.0, y=0, relheight=1.0, width=g, anchor="ne")
            abajo.place(x=0, rely=1.0, relwidth=1.0, height=g, anchor="nw")
        except tk.TclError:
            pass

    def _rainbow_iniciar(self):
        """Activa el arcoíris de bordes: muestra el marco y arranca el
        ciclo LENTO (la paleta del usuario no se toca)."""
        if getattr(self, "_rainbow_activo", False):
            return
        self._rainbow_activo = True
        self._rainbow_fase = 0.0
        self._rainbow_ultimo = time.time()
        self._marco_arcoiris_colocar()
        try:
            self.root.after(100, self._rainbow_tick)
        except tk.TclError:
            pass

    def _rainbow_tick(self):
        """Un paso del ciclo: avanza el tono poco a poco y pinta las 4
        franjas del borde. Con ola, cada lado va desfasado del siguiente
        (transición suave, no un salto)."""
        if not getattr(self, "_rainbow_activo", False):
            return
        ahora = time.time()
        dt = min(0.5, max(0.0, ahora - self._rainbow_ultimo))
        self._rainbow_ultimo = ahora
        vel = self._rainbow_estado.get("velocidad", 3)
        # muy lento: a velocidad 10 una vuelta completa tarda ~12 s
        self._rainbow_fase = (self._rainbow_fase + dt * 0.008 * vel) % 1.0
        ola = self._rainbow_estado.get("ola", True)
        for i, f in enumerate(getattr(self, "_marco_bordes", [])):
            h = self._rainbow_fase
            if ola:
                h = (h + i * 0.09) % 1.0    # desfase suave entre lados
            r, g, b = colorsys.hsv_to_rgb(h, 0.85, 1.0)
            try:
                f.config(bg=f"#{int(r * 255):02x}"
                             f"{int(g * 255):02x}{int(b * 255):02x}")
            except tk.TclError:
                pass
        try:
            self.root.after(100, self._rainbow_tick)
        except tk.TclError:
            self._rainbow_activo = False

    def _rainbow_parar(self, guardar=True):
        """Desactiva el arcoíris: oculta el marco (la paleta estática
        nunca cambió)."""
        if not getattr(self, "_rainbow_activo", False):
            return
        self._rainbow_activo = False
        for f in getattr(self, "_marco_bordes", []):
            try:
                f.place_forget()
            except tk.TclError:
                pass
        if guardar:
            self._guardar_colores()

    def _refrescar_combo_secciones(self):
        try:
            self.combo_seccion.config(values=["Todas"] + self.secciones)
        except (AttributeError, tk.TclError):
            pass    # UI todavía no construida

    def _asignar_seccion_nueva(self, name):
        """Canciones nuevas caen en la sección del filtro activo (si hay
        uno distinto de Todas/General), así aparecen al instante."""
        try:
            sec = self.seccion_filter_var.get()
        except (AttributeError, tk.TclError):
            return
        if (sec and sec not in ("Todas", "General")
                and name not in self.seccion_de):
            self.seccion_de[name] = sec
            self._guardar_secciones()

    def _mover_a_seccion(self, name, seccion):
        self._mover_a_seccion_multi([name], seccion)

    def _mover_a_seccion_multi(self, nombres, seccion):
        """Mueve UNA O VARIAS canciones a una sección de una sola vez."""
        if seccion not in self.secciones:
            return
        movidos = [n for n in nombres if n in self.scores]
        if not movidos:
            return
        for n in movidos:
            self.seccion_de[n] = seccion
        self._guardar_secciones()
        # si la activa se movió, que quede visible tras el filtro
        actual = getattr(self, "_score_actual", None)
        keep = actual if (actual in movidos and
                          self.seccion_filter_var.get() in (seccion, "Todas")
                          ) else movidos[0]
        self._refresh_list(keep=keep)
        if len(movidos) == 1:
            self.lbl_estado.config(
                text=f"📂 '{movidos[0]}' → sección '{seccion}'")
        else:
            self.lbl_estado.config(
                text=f"📂 {len(movidos)} canciones → sección '{seccion}'")

    def _dnd_press(self, evt):
        """Botón presionado sobre la lista: preparamos el arrastre.
        - Ctrl/Shift: no intervenimos (Tk agrega/extiende la selección).
        - Item NO seleccionado: se selecciona solo él y ya se puede
          arrastrar directo (sin tener que hacer clic antes).
        - Item YA seleccionado: se conserva la multi-selección y se
          arrastran TODAS las elegidas (clic sin arrastrar = colapsar).
        """
        self._dnd = None
        idx = self.listbox.nearest(evt.y)
        if idx < 0:
            return
        sel = list(self.listbox.curselection())
        ya_sel = idx in sel
        if evt.state & 0x0005:      # Ctrl=0x4, Shift=0x1: nativo
            return
        if not ya_sel:
            # clic sobre una no seleccionada: la activamos YA (así el
            # arrastre parte de una selección real) y bloqueamos el
            # comportamiento nativo de "extender al arrastrar"
            self.listbox.selection_clear(0, "end")
            self.listbox.selection_set(idx)
            self.listbox.activate(idx)
            self._on_select_score()
            sel = [idx]
        self._dnd = {"idx": idx, "sel": sel, "ya_sel": ya_sel,
                     "start": (evt.x_root, evt.y_root), "moved": False}
        return "break"

    def _dnd_motion(self, evt):
        if self._dnd is None:
            # RESCATE: el press no preparó el drag (modificador pegado,
            # clic de otra vía…) pero el botón sigue apretado sobre una
            # canción seleccionada: arrancamos el drag AHORA
            try:
                if not (evt.state & 0x100):     # botón izq. apretado
                    return
                sel = list(self.listbox.curselection())
                idx = self.listbox.nearest(evt.y)
                if not sel or idx < 0 or idx not in sel:
                    return
                self._dnd = {"idx": idx, "sel": sel, "ya_sel": True,
                             "start": (evt.x_root, evt.y_root),
                             "moved": False}
            except tk.TclError:
                return
        d = self._dnd
        dx = evt.x_root - d["start"][0]
        dy = evt.y_root - d["start"][1]
        if not d["moved"] and dx * dx + dy * dy < 100:
            return "break"      # todavía es solo un click
        d["moved"] = True
        # SIN ventanita flotante (en Windows puede robar el mouse):
        # el aviso va a la barra de estado de la ventana principal
        try:
            self.lbl_estado.config(
                text=f"📤 {len(d['sel'])} canción(es) — soltá para "
                     "elegir la carpeta destino")
        except (tk.TclError, AttributeError):
            pass
        return "break"

    def _dnd_release(self, evt):
        d = self._dnd
        self._dnd = None
        if not d:
            return
        if not d["moved"]:
            if d["ya_sel"]:
                # click simple (sin arrastre) sobre ya seleccionada:
                # colapsar la selección a esa canción
                self.listbox.selection_clear(0, "end")
                self.listbox.selection_set(d["idx"])
                self.listbox.activate(d["idx"])
                self._on_select_score()
            return
        # arrastre real: da IGUAL dónde se suelte — aparece el menú para
        # elegir la carpeta destino (a prueba de puntería)
        nombres = []
        for i in d["sel"]:
            if 0 <= i < self.listbox.size():
                nombres.append(self.listbox.get(i))
        if not nombres:
            return
        self._elegir_destino_y_mover(nombres, evt.x_root, evt.y_root)

    def _mover_con_tecla(self, _evt=None):
        """Tecla M con canciones seleccionadas en la lista: abre el
        mini-menú de carpeta destino junto al item."""
        sel = list(self.listbox.curselection())
        nombres = [self.listbox.get(i) for i in sel
                   if 0 <= i < self.listbox.size()]
        if not nombres:
            return "break"
        try:
            x, y, w, h = self.listbox.bbox(sel[-1])
        except (tk.TclError, ValueError):
            return "break"
        self._elegir_destino_y_mover(
            nombres, self.listbox.winfo_rootx() + x + w + 12,
            self.listbox.winfo_rooty() + y)
        return "break"

    def _elegir_destino_y_mover(self, nombres, x_root, y_root):
        """Mini-menú para elegir la carpeta destino tras arrastrar
        canciones (se abre donde se suelten, sin apuntar a nada)."""
        m = tk.Menu(self.listbox, tearoff=0, bg="#333333", fg="white",
                    font=("Segoe UI", 10))
        titulo = (f"Mover {len(nombres)} canción(es) a:"
                  if len(nombres) > 1 else "Mover a:")
        m.add_command(label=titulo, state="disabled",
                      background="#222222", foreground="#ffe066")
        for s in self.secciones:
            m.add_command(label=f"📂 {s}",
                          command=lambda s=s: self._mover_a_seccion_multi(
                              nombres, s))
        m.add_separator()
        m.add_command(label="➕ Nueva sección y mover ahí…",
                      command=lambda: self._mover_a_seccion_nueva(nombres))
        m.add_separator()
        m.add_command(label="✖ Cancelar",
                      command=lambda: None)
        try:
            m.tk_popup(x_root, y_root)
        finally:
            try:
                m.grab_release()
            except tk.TclError:
                pass

    def _menu_lista(self, evt):
        """Clic derecho sobre la lista: mover a sección / renombrar /
        duplicar / eliminar. Respeta la multi-selección (Ctrl/Shift)."""
        idx = self.listbox.nearest(evt.y)
        sel = list(self.listbox.curselection())
        if idx >= 0 and idx not in sel:
            # el item bajo el cursor no estaba entre las elegidas:
            # seleccionar SOLO ese (como en el explorador de archivos)
            self.listbox.selection_clear(0, "end")
            self.listbox.selection_set(idx)
            sel = [idx]
        if idx >= 0:
            self.listbox.activate(idx)
        nombres = [self.listbox.get(i) for i in sel
                   if 0 <= i < self.listbox.size()]
        if not nombres:
            return
        self._on_select_score()
        m = tk.Menu(self.listbox, tearoff=0, bg="#333333", fg="white",
                    font=("Segoe UI", 10))
        sub = tk.Menu(m, tearoff=0, bg="#333333", fg="white",
                      font=("Segoe UI", 10))
        secciones_actuales = {self.seccion_de.get(n, "General")
                              for n in nombres}
        destino_lbl = ("📂 Mover a sección" if len(nombres) == 1
                       else f"📂 Mover {len(nombres)} canciones a…")
        for s in self.secciones:
            if s not in secciones_actuales:
                sub.add_command(
                    label=f"📂 {s}",
                    command=lambda s=s: self._mover_a_seccion_multi(nombres, s))
        sub.add_separator()
        sub.add_command(label="➕ Nueva sección y mover ahí…",
                        command=lambda: self._mover_a_seccion_nueva(nombres))
        m.add_cascade(label=destino_lbl, menu=sub)
        m.add_separator()
        m.add_command(label="🔁 Renombrar", command=self._rename_score)
        m.add_command(label="⧉ Duplicar", command=self._duplicate_score)
        m.add_command(label="🗑 Eliminar", command=self._delete_score)
        try:
            m.tk_popup(evt.x_root, evt.y_root)
        finally:
            m.grab_release()
        return "break"

    def _mover_a_seccion_nueva(self, nombres):
        nueva = self._crear_seccion_dialog()
        if nueva:
            self._mover_a_seccion_multi(nombres, nueva)

    def _crear_seccion_dialog(self):
        """Pide un nombre y crea la sección. Devuelve el nombre o None."""
        while True:
            n = simpledialog.askstring(
                "Nueva sección",
                "Nombre de la sección nueva (carpeta de canciones):",
                parent=self.root)
            if n is None:
                return None
            n = n.strip()
            if not n:
                return None
            if n in self.secciones:
                messagebox.showwarning("AutoPiano",
                                       "Ya existe una sección con ese nombre.")
                continue
            self.secciones.append(n)
            self._guardar_secciones()
            self._refrescar_combo_secciones()
            return n

    def _dialogo_colores(self):
        """🎨 Editor de la paleta: elegí un elemento en la lista y
        cambiá su color con código hex (#ffffff), con las barras RGB
        o con el selector de Windows. Todo se guarda al instante."""
        win = tk.Toplevel(self.root)
        win.title("🎨 Colores")
        win.geometry("560x545")
        win.configure(bg="#2b2b2b")

        tk.Label(win, text="🎨 Colores de la app", bg="#2b2b2b", fg="white",
                 font=("Segoe UI", 13, "bold")).pack(anchor="w", padx=14,
                                                     pady=(10, 4))

        cuerpo = tk.Frame(win, bg="#2b2b2b")
        cuerpo.pack(fill="both", expand=True, padx=14)

        # --- izquierda: lista de elementos ---
        izq = tk.Frame(cuerpo, bg="#2b2b2b")
        izq.pack(side="left", fill="y")
        tk.Label(izq, text="Elemento:", bg="#2b2b2b", fg="#cccccc",
                 font=("Segoe UI", 10)).pack(anchor="w", pady=(0, 2))
        lb = tk.Listbox(izq, height=12, width=24, bg="#1e1e1e",
                        fg="#e8e8e8", selectbackground="#4a6da7",
                        font=("Segoe UI", 10), exportselection=False)
        lb.pack(fill="y", expand=True)
        for k in self.colores:
            lb.insert("end", k)
        lb.selection_set(0)

        # --- derecha: editor del elemento elegido ---
        der = tk.Frame(cuerpo, bg="#2b2b2b")
        der.pack(side="left", fill="both", expand=True, padx=(14, 0))

        lbl_nombre = tk.Label(der, text="", bg="#2b2b2b", fg="white",
                              font=("Segoe UI", 11, "bold"))
        lbl_nombre.pack(anchor="w")
        muestra = tk.Canvas(der, width=140, height=44, highlightthickness=0,
                            bg="#000000")
        muestra.pack(anchor="w", pady=6)

        fila_hex = tk.Frame(der, bg="#2b2b2b")
        fila_hex.pack(fill="x", pady=(2, 0))
        tk.Label(fila_hex, text="Código HEX:", bg="#2b2b2b", fg="#cccccc",
                 font=("Segoe UI", 10)).pack(side="left")
        entry_hex = tk.Entry(fila_hex, width=10, font=("Consolas", 12),
                             bg="#1e1e1e", fg="#e8e8e8",
                             insertbackground="white")
        entry_hex.pack(side="left", padx=6)
        tk.Label(fila_hex, text="(o R,G,B)", bg="#2b2b2b", fg="#888888",
                 font=("Segoe UI", 8, "italic")).pack(side="left")

        escalas = {}
        for canal in ("R", "G", "B"):
            fila = tk.Frame(der, bg="#2b2b2b")
            fila.pack(fill="x", pady=2)
            tk.Label(fila, text=f"{canal}:", bg="#2b2b2b", fg="#cccccc",
                     font=("Segoe UI", 10), width=2).pack(side="left")
            var = tk.IntVar(value=0)
            esc = ttk.Scale(fila, from_=0, to=255, variable=var,
                            length=200)
            esc.pack(side="left", fill="x", expand=True, padx=6)
            lbl_val = tk.Label(fila, text="0", bg="#2b2b2b", fg="#e8e8e8",
                               font=("Segoe UI", 9), width=3)
            lbl_val.pack(side="left")
            escalas[canal] = (var, esc, lbl_val)

        estado = tk.Label(win, text="", bg="#2b2b2b", fg="#ffe066",
                          font=("Segoe UI", 9))
        estado.pack(anchor="w", padx=14)

        clave = {"nombre": list(self.colores)[0] if self.colores else ""}

        def refrescar_editor():
            """Carga en el editor el color del elemento elegido."""
            k = clave["nombre"]
            if not k:
                return
            lbl_nombre.config(text=k)
            hexv = self.colores.get(k, "#000000")
            entry_hex.delete(0, "end")
            entry_hex.insert(0, hexv)
            r, g, b = self._hex_a_rgb(hexv)
            for canal, val in (("R", r), ("G", g), ("B", b)):
                var, esc, lbl_val = escalas[canal]
                var.set(val)
                lbl_val.config(text=str(val))
            muestra.config(bg=hexv)

        def aplicar(nuevo_hex, avisar=True):
            """Valida, guarda, aplica y actualiza la UI."""
            k = clave["nombre"]
            if not k or not self._hex_valido(nuevo_hex):
                if avisar:
                    estado.config(
                        text="⚠ Formato: #ffffff o 255,255,255")
                return False
            self.colores[k] = nuevo_hex.lower()
            self._guardar_colores()
            self._aplicar_colores()
            muestra.config(bg=nuevo_hex.lower())
            if avisar:
                estado.config(text=f"✔ {k} = {nuevo_hex.lower()}")
            return True

        def desde_entry(_evt=None):
            txt = entry_hex.get().strip()
            m = re.fullmatch(r"(\d{1,3})\s*,\s*(\d{1,3})\s*,\s*(\d{1,3})",
                             txt)     # estilo RGB: 255,255,255
            if m:
                r, g, b = (max(0, min(255, int(x)))
                           for x in m.groups())
                txt = self._rgb_a_hex(r, g, b)
            if aplicar(txt):
                refrescar_editor()
            return "break"

        def desde_escalas(_evt=None):
            vals = [escalas[c][0].get() for c in ("R", "G", "B")]
            hexv = self._rgb_a_hex(*vals)
            for canal, val in zip(("R", "G", "B"), vals):
                escalas[canal][2].config(text=str(int(val)))
            # aplicar SIN avisar (los scales disparan seguido)
            k = clave["nombre"]
            if k and self._hex_valido(hexv):
                self.colores[k] = hexv
                self._aplicar_colores()
                muestra.config(bg=hexv)
                entry_hex.delete(0, "end")
                entry_hex.insert(0, hexv)

        def guardar_escalas(_evt=None):
            self._guardar_colores()
            estado.config(text=f"✔ Guardado: {clave['nombre']} = "
                               f"{self.colores.get(clave['nombre'], '')}")

        def elegir_sistema():
            k = clave["nombre"]
            rgb, hexv = colorchooser.askcolor(
                color=self.colores.get(k, "#ffffff"), parent=win,
                title=f"Elegir color: {k}")
            if hexv:
                if aplicar(str(hexv)):
                    refrescar_editor()

        def restaurar():
            if messagebox.askyesno(
                    "Restaurar colores",
                    "¿Volver a los colores originales de la app?",
                    parent=win):
                if getattr(self, "_rainbow_activo", False):
                    self._rainbow_parar(guardar=False)
                    var_act.set(False)
                self.colores = dict(COLORES_DEFAULT)
                self._guardar_colores()
                self._aplicar_colores()
                refrescar_editor()
                estado.config(text="✔ Colores originales restaurados")

        def arcoiris_toggle():
            self._rainbow_estado["activado"] = bool(var_act.get())
            if var_act.get():
                self._rainbow_iniciar()
                estado.config(
                    text="🌈 Arcoíris SOLO en los bordes — tu paleta "
                         "no se toca")
            else:
                self._rainbow_parar()
                estado.config(text="✔ Arcoíris apagado")
            self._guardar_colores()

        def arcoiris_ola():
            self._rainbow_estado["ola"] = bool(var_ola.get())
            self._guardar_colores()

        def velocidad_cambio(_v=None):
            v = min(10, max(1, int(round(var_vel.get()))))
            self._rainbow_estado["velocidad"] = v
            lbl_vel.config(text=str(v))

        def velocidad_guardar(_evt=None):
            self._guardar_colores()

        # --- modo arcoíris 🌈 ----------------------------------------------
        rb_frame = tk.LabelFrame(win, text="🌈 Borde arcoíris", bg="#2b2b2b",
                                 fg="#ffe066",
                                 font=("Segoe UI", 10, "bold"))
        rb_frame.pack(fill="x", padx=14, pady=(6, 0))
        var_act = tk.BooleanVar(value=self._rainbow_estado.get("activado",
                                                                False))
        var_ola = tk.BooleanVar(value=self._rainbow_estado.get("ola", True))
        fila_r = tk.Frame(rb_frame, bg="#2b2b2b")
        fila_r.pack(fill="x", padx=8, pady=(4, 2))
        chk_act = tk.Checkbutton(fila_r, text="Activar (solo los bordes)",
                                 variable=var_act,
                                 command=arcoiris_toggle, bg="#2b2b2b",
                                 fg="white", activebackground="#2b2b2b",
                                 activeforeground="#ffe066",
                                 selectcolor="#1e1e1e",
                                 font=("Segoe UI", 10))
        chk_act.pack(side="left")
        chk_ola = tk.Checkbutton(fila_r,
                                 text="Efecto ola 🌊 (gradual)",
                                 variable=var_ola,
                                 command=arcoiris_ola, bg="#2b2b2b",
                                 fg="#cccccc", activebackground="#2b2b2b",
                                 activeforeground="#ffe066",
                                 selectcolor="#1e1e1e",
                                 font=("Segoe UI", 9))
        chk_ola.pack(side="left", padx=(10, 0))
        fila_v = tk.Frame(rb_frame, bg="#2b2b2b")
        fila_v.pack(fill="x", padx=8, pady=(0, 6))
        tk.Label(fila_v, text="Velocidad:", bg="#2b2b2b", fg="#cccccc",
                 font=("Segoe UI", 9)).pack(side="left")
        var_vel = tk.DoubleVar(value=self._rainbow_estado.get("velocidad", 3))
        esc_vel = ttk.Scale(fila_v, from_=1, to=10, variable=var_vel,
                            length=180)
        esc_vel.pack(side="left", fill="x", expand=True, padx=6)
        lbl_vel = tk.Label(fila_v, text=str(self._rainbow_estado.get(
            "velocidad", 3)), bg="#2b2b2b", fg="#e8e8e8",
            font=("Segoe UI", 9), width=2)
        lbl_vel.pack(side="left")

        entry_hex.bind("<Return>", desde_entry)
        for canal in ("R", "G", "B"):
            var, esc, _l = escalas[canal]
            esc.config(command=desde_escalas)
            esc.bind("<ButtonRelease-1>", guardar_escalas)
            var.trace_add("write", lambda *a, c=canal: desde_escalas())

        def al_elegir(_evt=None):
            sel = lb.curselection()
            if sel:
                clave["nombre"] = list(self.colores)[sel[0]]
                refrescar_editor()
                estado.config(text="")
        lb.bind("<<ListboxSelect>>", al_elegir)

        botones = tk.Frame(win, bg="#2b2b2b")
        botones.pack(fill="x", padx=14, pady=(6, 8))
        tk.Button(botones, text="🎯 Elegir del sistema", command=elegir_sistema,
                  bg="#3a5a7d", fg="white", relief="flat").pack(side="left")
        tk.Button(botones, text="♻ Restaurar originales", command=restaurar,
                  bg="#8b3a3a", fg="white", relief="flat"
                  ).pack(side="left", padx=6)
        tk.Button(win, text="Cerrar", command=win.destroy, bg="#777777",
                  fg="white", relief="flat").pack(pady=(0, 10))

        esc_vel.config(command=velocidad_cambio)
        esc_vel.bind("<ButtonRelease-1>", velocidad_guardar)
        refrescar_editor()

    def _dialogo_secciones(self):
        """Gestor de secciones TODO-EN-UNO: a la izquierda las canciones
        (con su carpeta actual), a la derecha las carpetas. Se seleccionan
        canciones acá mismo y se mueven con el botón verde o arrastrando
        hasta una carpeta. También crea/renombra/elimina carpetas. Cualquier
        cambio refresca la lista principal al instante."""
        win = tk.Toplevel(self.root)
        win.title("📂 Secciones")
        win.geometry("640x470")
        win.configure(bg="#2b2b2b")
        # SIN grab_set: NO es modal

        tk.Label(win, text="📂 Secciones", bg="#2b2b2b", fg="white",
                 font=("Segoe UI", 13, "bold")).pack(anchor="w", padx=14,
                                                     pady=(10, 4))

        cuerpo = tk.Frame(win, bg="#2b2b2b")
        cuerpo.pack(fill="both", expand=True, padx=14)

        # ---------- columna izquierda: CANCIONES ----------
        izq = tk.Frame(cuerpo, bg="#2b2b2b")
        izq.pack(side="left", fill="both", expand=True)
        fila_ver = tk.Frame(izq, bg="#2b2b2b")
        fila_ver.pack(fill="x", pady=(0, 2))
        tk.Label(fila_ver, text="Canciones — Ver:", bg="#2b2b2b",
                 fg="#cccccc", font=("Segoe UI", 10)).pack(side="left")
        ver_var = tk.StringVar(value="General")
        combo_ver = ttk.Combobox(fila_ver, textvariable=ver_var,
                                 state="readonly", width=12)
        combo_ver.pack(side="left", padx=(6, 0))
        tk.Label(izq, text="(Ctrl+clic para varias):",
                 bg="#2b2b2b", fg="#888888",
                 font=("Segoe UI", 8, "italic")).pack(anchor="w")
        fila_c = tk.Frame(izq, bg="#2b2b2b")
        fila_c.pack(fill="both", expand=True)
        sb_c = tk.Scrollbar(fila_c)
        sb_c.pack(side="right", fill="y")
        lb_c = tk.Listbox(fila_c, height=14, bg="#1e1e1e", fg="#e8e8e8",
                          selectbackground="#3a7d44",
                          selectmode="extended", font=("Segoe UI", 10),
                          exportselection=False,
                          yscrollcommand=sb_c.set)
        lb_c.pack(side="left", fill="both", expand=True)
        sb_c.config(command=lb_c.yview)

        # ---------- columna derecha: CARPETAS ----------
        der = tk.Frame(cuerpo, bg="#2b2b2b")
        der.pack(side="left", fill="both", expand=True, padx=(10, 0))
        tk.Label(der, text="Carpetas:", bg="#2b2b2b", fg="#cccccc",
                 font=("Segoe UI", 10)).pack(anchor="w", pady=(0, 2))
        lb = tk.Listbox(der, height=14, bg="#1e1e1e", fg="#e8e8e8",
                        selectbackground="#4a6da7", font=("Segoe UI", 10),
                        exportselection=False)
        lb.pack(fill="both", expand=True)

        estado = tk.Label(win, text="", bg="#2b2b2b", fg="#ffe066",
                          font=("Segoe UI", 9))
        estado.pack(anchor="w", padx=14)

        def nombres_de_indices(idxs):
            """Nombres reales a partir de los índices del listbox de
            canciones (el texto mostrado tiene la carpeta pegada)."""
            out = []
            for i in idxs:
                if 0 <= i < lb_c.size():
                    out.append(lb_c.get(i).split("   —   ")[0])
            return out

        def poblar_canciones():
            """Llena la lista de canciones según el filtro 'Ver:' (por
            defecto General: solo las que no están en ninguna carpeta,
            así no confunden a las ya organizadas)."""
            ver = ver_var.get() or "Todas"
            lb_c.delete(0, "end")
            for n in sorted(self.scores, key=str.lower):
                if ver != "Todas" and self.seccion_de.get(n, "General") \
                        != ver:
                    continue
                lb_c.insert("end", f"{n}   —   "
                                   f"{self.seccion_de.get(n, 'General')}")

        def refrescar(keep_sec=None):
            """Repinta las dos listas con lo actual (canciones A-Z con su
            carpeta; carpetas con conteo) y la lista principal."""
            combo_ver.config(values=["Todas"] + list(self.secciones))
            poblar_canciones()
            lb.delete(0, "end")
            for s in self.secciones:
                # cuenta TODAS las canciones de la carpeta (incluidas las
                # que están en General sin asignación explícita)
                cuantas = sum(1 for n in self.scores
                              if self.seccion_de.get(n, "General") == s)
                lb.insert("end", f"{s}   ({cuantas})")
            if keep_sec and keep_sec in self.secciones:
                lb.selection_clear(0, "end")
                lb.selection_set(self.secciones.index(keep_sec))
            else:
                lb.selection_set(0)
            self._refrescar_combo_secciones()
            self._refresh_list()
            self._refrescar_barra_seccion()

        def elegida():
            sel = lb.curselection()
            if not sel:
                return None
            return self.secciones[sel[0]]

        def mover(nombres=None, sec=None):
            """Mueve canciones a una carpeta y refresca TODO."""
            if not nombres:
                nombres = nombres_de_indices(lb_c.curselection())
                if not nombres:
                    # respaldo: la selección de la lista principal
                    nombres = [self.listbox.get(i)
                               for i in self.listbox.curselection()
                               if 0 <= i < self.listbox.size()]
            if not sec:
                sec = elegida()
            if not nombres or not sec:
                estado.config(text="⚠ Elegí canción(es) y una carpeta")
                return
            self._mover_a_seccion_multi(nombres, sec)
            refrescar(keep_sec=sec)
            estado.config(text=f"✔ {len(nombres)} canción(es) → "
                               f"{sec}")

        # ---- arrastre DENTRO de esta ventana: canciones -> carpeta ----
        dnd = {"start": None, "moved": False}

        def dnd_press(evt):
            dnd["start"] = (evt.x_root, evt.y_root)
            dnd["moved"] = False
            idx = lb_c.nearest(evt.y)
            if idx < 0:
                return
            sel = list(lb_c.curselection())
            if idx not in sel and not (evt.state & 0x0005):
                lb_c.selection_clear(0, "end")
                lb_c.selection_set(idx)

        def dnd_motion(evt):
            if not dnd["start"]:
                return
            dx = evt.x_root - dnd["start"][0]
            dy = evt.y_root - dnd["start"][1]
            if not dnd["moved"] and dx * dx + dy * dy < 100:
                return
            dnd["moved"] = True
            n = len(nombres_de_indices(lb_c.curselection())) or 1
            estado.config(text=f"📤 {n} canción(es) — soltá sobre una "
                               "carpeta de la derecha")

        def sobre_carpetas(evt):
            try:
                x0, y0 = lb.winfo_rootx(), lb.winfo_rooty()
            except tk.TclError:
                return False
            return (x0 <= evt.x_root <= x0 + lb.winfo_width()
                    and y0 <= evt.y_root <= y0 + lb.winfo_height())

        def dnd_release(evt):
            inicio = dnd["start"]
            dnd["start"] = None
            if not inicio or not dnd["moved"]:
                return
            if not sobre_carpetas(evt):
                estado.config(text="")
                return
            sel = lb.curselection()
            if not sel:
                estado.config(text="⚠ Elegí primero una carpeta de la "
                                   "derecha")
                return
            mover(nombres=nombres_de_indices(lb_c.curselection()),
                  sec=self.secciones[sel[0]])

        lb_c.bind("<ButtonPress-1>", dnd_press, add="+")
        lb_c.bind("<B1-Motion>", dnd_motion, add="+")
        lb_c.bind("<ButtonRelease-1>", dnd_release, add="+")
        combo_ver.bind("<<ComboboxSelected>>",
                       lambda e: poblar_canciones())

        def nueva():
            n = self._crear_seccion_dialog()
            if n:
                refrescar(keep_sec=n)
                estado.config(text=f"✔ Carpeta '{n}' creada")

        def renombrar():
            sec = elegida()
            if not sec:
                return
            if sec == "General":
                messagebox.showinfo("AutoPiano",
                                    "'General' es la sección base y no se "
                                    "puede renombrar.")
                return
            nuevo = simpledialog.askstring(
                "Renombrar sección", f"Nuevo nombre para '{sec}':",
                initialvalue=sec, parent=win)
            if not nuevo or nuevo.strip() == sec:
                return
            nuevo = nuevo.strip()
            if nuevo in self.secciones:
                messagebox.showwarning("AutoPiano",
                                       "Ya existe una sección con ese nombre.")
                return
            self.secciones[self.secciones.index(sec)] = nuevo
            self.seccion_de = {k: (nuevo if v == sec else v)
                               for k, v in self.seccion_de.items()}
            if self.seccion_filter_var.get() == sec:
                self.seccion_filter_var.set(nuevo)
            self._guardar_secciones()
            refrescar(keep_sec=nuevo)
            estado.config(text=f"✔ Carpeta renombrada a '{nuevo}'")

        def eliminar():
            sec = elegida()
            if not sec:
                return
            if sec == "General":
                messagebox.showinfo("AutoPiano",
                                    "'General' es la sección base y no se "
                                    "puede eliminar.")
                return
            cuantas = sum(1 for v in self.seccion_de.values() if v == sec)
            if not messagebox.askyesno(
                    "Eliminar sección",
                    f"¿Eliminar la sección '{sec}'?\n\n"
                    f"Las {cuantas} canción(es) que contiene vuelven a "
                    "'General' (no se borra ninguna canción)."):
                return
            self.secciones.remove(sec)
            self.seccion_de = {k: ("General" if v == sec else v)
                               for k, v in self.seccion_de.items()}
            if self.seccion_filter_var.get() == sec:
                self.seccion_filter_var.set("Todas")
            self._guardar_secciones()
            refrescar()
            estado.config(text=f"✔ Carpeta '{sec}' eliminada")

        botones = tk.Frame(win, bg="#2b2b2b")
        botones.pack(fill="x", padx=14, pady=(6, 8))
        tk.Button(botones, text="➡ Mover a la carpeta", command=mover,
                  bg="#3a7d44", fg="white", relief="flat",
                  font=("Segoe UI", 10, "bold")).pack(side="left",
                                                      padx=(0, 6))
        tk.Button(botones, text="➕ Nueva", command=nueva, bg="#3a5a7d",
                  fg="white", relief="flat").pack(side="left", padx=3)
        tk.Button(botones, text="✏ Renombrar", command=renombrar,
                  bg="#555555", fg="white", relief="flat").pack(side="left",
                                                               padx=3)
        tk.Button(botones, text="🗑 Eliminar", command=eliminar,
                  bg="#8b3a3a", fg="white", relief="flat").pack(side="left",
                                                               padx=3)
        tk.Button(win, text="Cerrar", command=win.destroy, bg="#777777",
                  fg="white", relief="flat").pack(pady=(0, 10))

        refrescar()

    # ======================================================================
    # Reproducción
    # ======================================================================
    # ======================================================================
    # v4.23 — Tramo A→B: repetir la parte difícil en bucle
    # ======================================================================
    def _tramo(self):
        """(a, b) del tramo marcado y válido, o (None, None)."""
        a, b = self._marca_a, self._marca_b
        if a is None or b is None:
            return None, None
        if b < a:
            a, b = b, a              # si marcó al revés, se ordena solo
        return a, b

    def _marcar_tramo(self, cual):
        """📍A / 📍B: marca el inicio o el fin del tramo a repetir. Si está
        sonando, toca el grupo actual; si no, la posición del cursor."""
        if not self.groups:
            messagebox.showinfo("Tramo A→B",
                                "No hay notas en el pizarrón todavía.")
            return
        pos = self.pos if self.playing else self._cursor_group_pos()
        pos = min(max(pos, 0), len(self.groups) - 1)
        if cual == "A":
            self._marca_a = pos
        else:
            self._marca_b = pos
        a, b = self._tramo()
        if a is None:
            self.lbl_tramo.config(text="Tramo: —", fg="#888888")
        elif a == b:
            self.lbl_tramo.config(
                text="Tramo: 1 nota (repite sola)", fg="#ff9f6b")
        else:
            self.lbl_tramo.config(
                text=f"Tramo: notas {a + 1} → {b + 1} (en bucle)",
                fg="#ff9f6b")
        if a is not None and b is not None and a != b:
            self.lbl_estado.config(text=f"🔁 Tramo A→B: notas {a + 1}–{b + 1}")

    def _limpiar_tramo(self):
        """✖: quita los marcadores A/B (vuelve a tocar la canción entera)."""
        self._marca_a = None
        self._marca_b = None
        self.lbl_tramo.config(text="Tramo: —", fg="#888888")
        if not self.playing:
            self.lbl_estado.config(text="Listo")

    def _limpiar_tramo_al_cambiar(self):
        """Se usa al cambiar de canción: los marcadores no aplican."""
        if self._marca_a is not None or self._marca_b is not None:
            self._limpiar_tramo()

    # ======================================================================
    # v4.23 — 📈 Récords por canción y racha de días
    # ======================================================================
    def _cargar_records(self):
        """Carga autopiano_records.json: {canciones: {nombre: {tocadas,
        completadas, mejor_vel}}, racha: {ultimo_dia, dias}}."""
        self.records = {"canciones": {}, "racha": {"ultimo_dia": "", "dias": 0}}
        if os.path.exists(RECORDS_FILE):
            try:
                with open(RECORDS_FILE, "r", encoding="utf-8-sig") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    canc = data.get("canciones")
                    if isinstance(canc, dict):
                        self.records["canciones"] = {
                            k: v for k, v in canc.items()
                            if isinstance(v, dict)}
                    racha = data.get("racha")
                    if isinstance(racha, dict):
                        self.records["racha"] = {
                            "ultimo_dia": str(racha.get("ultimo_dia", "")),
                            "dias": int(racha.get("dias", 0) or 0)}
            except Exception:
                pass

    def _guardar_records(self):
        try:
            _escribe_json(RECORDS_FILE, self.records)
        except Exception:
            pass

    def _registrar_toco(self):
        """Al apretar ▶: +1 tocadas a la canción actual y actualiza la
        racha de días seguidos (hoy / ayer / se rompió)."""
        name = self._score_actual or "—"
        canc = self.records.setdefault("canciones", {})
        fila = canc.setdefault(name, {"tocadas": 0, "completadas": 0,
                                      "mejor_vel": 0.0})
        fila["tocadas"] = int(fila.get("tocadas", 0)) + 1
        hoy = time.strftime("%Y-%m-%d")
        racha = self.records.setdefault(
            "racha", {"ultimo_dia": "", "dias": 0})
        ayer = time.strftime("%Y-%m-%d",
                             time.localtime(time.time() - 86400))
        if racha.get("ultimo_dia") == hoy:
            pass                         # ya contó hoy
        elif racha.get("ultimo_dia") == ayer:
            racha["dias"] = int(racha.get("dias", 0) or 0) + 1
        else:
            racha["dias"] = 1             # primer día (o se cortó la racha)
        racha["ultimo_dia"] = hoy
        self._guardar_records()

    def _registrar_exito(self):
        """Al terminar la canción bien: +1 completadas y guarda la mayor
        velocidad a la que se logró."""
        name = self._score_actual or "—"
        canc = self.records.setdefault("canciones", {})
        fila = canc.setdefault(name, {"tocadas": 0, "completadas": 0,
                                      "mejor_vel": 0.0})
        fila["completadas"] = int(fila.get("completadas", 0)) + 1
        try:
            vel = float(self.speed)
        except (ValueError, tk.TclError):
            vel = 0.0
        if vel > float(fila.get("mejor_vel", 0) or 0):
            fila["mejor_vel"] = round(vel, 2)
        self._guardar_records()

    def start_play(self):
        if self.playing:
            return
        if not PYNPUT_OK:
            messagebox.showerror("Falta pynput",
                                 "Instala la librería primero:\n\npip install pynput")
            return
        self.board.config(state="disabled")
        self._tag_groups(self.board.get("1.0", "end-1c"))
        if not self.groups:
            self.board.config(state="normal")
            messagebox.showwarning(
                "AutoPiano",
                "No hay notas en el pizarrón.\n"
                "Escribe letras (q w e r t y u…) y usa ( ) para acordes.")
            return
        self.pos = self._cursor_group_pos() if self.start_at_cursor else 0
        self.playing = True
        self.paused = False
        self.stop_flag = False
        self._registrar_toco()        # v4.23: récords (tocadas + racha)
        self._release_all_held()      # limpiar teclas de una sesión anterior
        self._update_progress()
        self.btn_play.config(state="disabled")
        self.btn_pause.config(state="normal", text="⏸  Pausar  (F6)")
        self.btn_stop.config(state="normal")
        if self.practice_mode:
            self._practice_keys.clear()
            self._start_practice_listener()
        threading.Thread(target=self._play_worker, daemon=True).start()

    def _cursor_group_pos(self):
        """Índice del grupo (nota/acorde) donde está el cursor del pizarrón:
        la primera nota que empieza en o después del cursor; si el cursor
        está dentro de un acorde, ese acorde. Si el cursor está al final
        (después de la última nota), arranca desde el principio."""
        text = self.board.get("1.0", "end-1c")
        offset = len(self.board.get("1.0", "insert"))
        for idx, (inicio, fin, _grupo) in enumerate(_tokenize_sheet(text)):
            if inicio >= offset or inicio <= offset < fin:
                return idx
        return 0

    def _play_worker(self):
        termino_ok = False
        try:
            for n in range(self.countdown, 0, -1):
                if self.stop_flag:
                    return
                self._ui(self.lbl_estado.config,
                         text=f"Tocando en {n}...\n(Cambia a Roblox)")
                time.sleep(1)

            self._ui(self.lbl_estado.config, text="▶ Reproduciendo")
            total = len(self.groups)
            vuelta = 1
            while True:
                self._ui(self.lbl_estado.config,
                         text=f"▶ Reproduciendo (vuelta {vuelta})"
                              if vuelta > 1 else "▶ Reproduciendo")
                while self.pos < total:
                    # --- v4.23: tramo A→B: pasó el fin -> vuelve al A ----
                    a, b = self._tramo()
                    if a is not None and self.pos > b:
                        self.pos = a
                        vuelta += 1
                        self._ui(self.lbl_estado.config,
                                 text=f"🔁 Tramo A→B (vuelta {vuelta})")
                    while self.paused and not self.stop_flag:
                        time.sleep(0.05)
                    if self.stop_flag:
                        break
                    self._ui(self._highlight, self.pos)
                    self._ui(self._update_progress)

                    notes = self.groups[self.pos]
                    if notes == ["-"]:            # pausa indicada en la partitura
                        self.pos += 1
                        if self.pos < total:
                            time.sleep(self.base_gap / max(self.speed, 0.1))
                        continue

                    # --- modo práctica: no toca la app, tocas TÚ -----------
                    if self.practice_mode:
                        if not self._wait_practice(notes):
                            break
                        self.pos += 1
                        time.sleep(0.05)
                        continue

                    var = self.realism  # 0.0 = robot exacto, 1.0 = muy humano

                    # --- presión de teclas (SIN bloquear el avance) ------------
                    # cada tecla se suelta sola después de su duración, en un
                    # hilo aparte: la canción avanza a su ritmo normal sin
                    # importar cuánto dure la tecla. Si una tecla ya está
                    # presionada y vuelve a salir, se suelta y se vuelve a
                    # presionar (así la repetición se escucha).
                    press_gap = random.uniform(0.0, 0.018) * var if len(notes) > 1 else 0
                    # primero las teclas simples/números y DESPUÉS las que
                    # necesitan Shift: así el toque de Shift nunca cae sobre
                    # un número/letra que el juego leería transformado
                    for k in sorted(notes, key=lambda x: _note_to_key(x)[1]):
                        hold = (self.hold_ms / 1000.0) * (1.0 + random.uniform(-var, var))
                        if random.random() < self.long_chance:  # notas largas
                            hold *= 1.0 + random.uniform(0.2, 0.9) * var
                        self._press_key_hold(k, max(hold, 0.03))
                        if press_gap:
                            time.sleep(random.uniform(0.0, press_gap))

                    self.pos += 1
                    if self.pos < total:
                        # separación entre notas también con variación humana,
                        # y de vez en cuando una pequeña "respiración" más larga
                        gap = (self.base_gap / max(self.speed, 0.1)) * (1.0 + random.uniform(-0.25, 0.25) * var)
                        if random.random() < self.breathe_chance:  # respiración
                            gap *= 1.0 + random.uniform(0.3, 1.2) * var
                        time.sleep(max(gap, 0.02))

                # --- ¿terminó, repite o cambia de canción? ------------------
                # v4.23: si el tramo A→B llega al fin de la canción (B en la
                # última nota), el bucle interno salió sin saltar: acá vuelve.
                a, b = self._tramo()
                if not self.stop_flag and a is not None and self.pos > b:
                    self.pos = a
                    vuelta += 1
                    self._ui(self.lbl_estado.config,
                             text=f"🔁 Tramo A→B (vuelta {vuelta})")
                    continue
                if self.stop_flag:
                    break
                if not self.loop_repeats and not self.rotate_songs:
                    termino_ok = True
                    self._ui(self._registrar_exito)   # v4.23: récord
                    self._ui(self.lbl_estado.config, text="✔ Terminado")
                    break
                vuelta += 1
                proximo = None
                if self.rotate_songs:
                    proximo = self._next_rotate_score()
                if proximo:
                    self._ui(self.lbl_estado.config,
                             text=f"🔁 Siguiente canción: {proximo} en 2 s…"
                                  " (F7 para salir)")
                else:
                    self._ui(self.lbl_estado.config,
                             text=f"🔁 Vuelta {vuelta} en 2 segundos…"
                                  " (F7 para salir)")
                for _ in range(20):               # 2 s entre vueltas
                    if self.stop_flag:
                        break
                    time.sleep(0.1)
                if self.stop_flag:
                    break
                if proximo:
                    # cambiar de partitura EN VIVO: se hace en el hilo de Tk
                    # y el worker espera a que esté cargada antes de seguir
                    self._cambio_event = threading.Event()
                    self._ui(self._cambiar_a_score_en_vivo, proximo)
                    self._cambio_event.wait(5)
                    self._release_all_held()      # no arrastrar notas
                self.pos = 0
                total = len(self.groups)          # la nueva canción puede
                # tener otra longitud: recalcular para no pasarse de largo
        except Exception as e:
            self._ui(self.lbl_estado.config, text=f"Error: {e}")
        finally:
            if not termino_ok:
                # detenido o con error: soltar las teclas que quedaron colgadas
                self._release_all_held()
            self._ui(self._playback_finished)

    def _next_rotate_score(self):
        """Siguiente partitura de la lista (para el bucle rotativo): la que
        sigue a la actual y, al final de la lista, vuelve a la primera."""
        orden = list(getattr(self, "_score_order", []))
        if not orden:
            return None
        try:
            i = orden.index(getattr(self, "_score_actual", None))
        except ValueError:
            return orden[0]      # el pizarrón tenía algo sin guardar
        return orden[(i + 1) % len(orden)]

    def _cambiar_a_score_en_vivo(self, name):
        """Carga la partitura `name` durante el bucle rotativo (hilo de Tk)
        y avisa al worker con self._cambio_event."""
        try:
            texto = self.scores.get(name)
            if texto is None:
                return
            self._score_actual = name
            self._limpiar_tramo_al_cambiar()   # v4.23: tramo de otra canción
            self._set_board_text(texto)
            self.board.config(state="disabled")
            self._tag_groups(self.board.get("1.0", "end-1c"))
            self._refresh_list(keep=name)
            # config personalizada de ESTA canción (si tiene)
            self._aplicar_song_overrides(name)
            self._ui(self.lbl_estado.config, text=f"▶ Reproduciendo: {name}")
        finally:
            self._cambio_event.set()

    def _playback_finished(self):
        self.playing = False
        self.paused = False
        self.board.config(state="normal")
        self.btn_play.config(state="normal")
        self.btn_pause.config(state="disabled", text="⏸  Pausar  (F6)")
        self.btn_stop.config(state="disabled")
        self._stop_practice_listener()
        self._schedule_autosave()   # por si quedó algo sin guardar
        if not self.lbl_estado.cget("text").startswith(("✔", "Error", "💾", "🔁", "✏")):
            self.lbl_estado.config(text="Listo")

    def _speed_hotkey(self, evt):
        """Teclas + y -: cambian la velocidad al instante, incluso mientras
        la canción suena (la próxima nota ya usa la nueva velocidad)."""
        try:
            v = float(self.speed_var.get())
        except (ValueError, tk.TclError):
            return
        if evt.keysym in ("plus", "KP_Add"):
            v += 0.25
        elif evt.keysym in ("minus", "KP_Subtract"):
            v -= 0.25
        else:
            return
        self.speed_var.set(round(min(max(v, 0.1), 20.0), 2))
        if self.playing:
            self.lbl_estado.config(text=f"⏩ Velocidad {self.speed:.2f}x en vivo")

    def toggle_pause(self):
        if not self.playing:
            return
        self.paused = not self.paused
        self.btn_pause.config(text="▶  Continuar  (F6)" if self.paused
                              else "⏸  Pausar  (F6)")
        self.lbl_estado.config(text="⏸ Pausado" if self.paused else "▶ Reproduciendo")

    def stop_play(self):
        if not self.playing:
            return
        self.stop_flag = True
        self.paused = False

    # ======================================================================
    # 📌 Modo compacto flotante: barrita chica SIEMPRE ENCIMA, para jugar
    # sin que la ventana grande tape el juego. Tiene ▶/⏸/⏹ y un botón
    # para volver a la app completa. Se arrastra con el mouse.
    # ======================================================================
    def _compacto_abrir(self):
        """Abre la barra compacta y oculta la ventana grande."""
        if getattr(self, "_compacto", None) is not None:
            self._compacto_cerrar()
            return
        fondo = self.colores.get("Fondo general", "#2b2b2b")
        acento = self.colores.get("Texto de acento", "#ffe9c9")
        win = tk.Toplevel(self.root)
        win.title("AutoPiano compacto")
        win.overrideredirect(True)           # sin marco: barrita pura
        win.attributes("-topmost", True)     # siempre encima de todo
        win.configure(bg=fondo)
        self._compacto = win
        # que NO se vea al transmitir pantalla (Discord/Zoom/OBS…)
        self._compacto_sin_transmision = self._compacto_ocultar_transmision(win)

        fila = tk.Frame(win, bg=fondo)
        fila.pack(padx=7, pady=5)
        lbl = tk.Label(fila, text="♪ AutoPiano", bg=fondo, fg=acento,
                       font=("Segoe UI", 9, "bold"), anchor="w")
        lbl.pack(side="left", padx=(0, 8))

        estilo = dict(width=3, relief="flat", font=("Segoe UI", 10),
                      bg="#5f3f1e", fg="#ffe9c9")
        b_play = tk.Button(fila, text="▶", command=self.start_play,
                           state="disabled", **estilo)
        b_play.pack(side="left", padx=1)
        b_pp = tk.Button(fila, text="⏸", command=self.toggle_pause,
                         state="disabled", **estilo)
        b_pp.pack(side="left", padx=1)
        b_stop = tk.Button(fila, text="⏹", command=self.stop_play,
                           state="disabled",
                           **{**estilo, "bg": "#8b3a3a"})
        b_stop.pack(side="left", padx=1)
        b_fan = tk.Button(fila, text="👻",
                          command=self._compacto_toggle_fantasma,
                          **{**estilo, "bg": "#5f3f1e"})
        b_fan.pack(side="left", padx=1)
        b_back = tk.Button(fila, text="🔍", command=self._compacto_cerrar,
                           **{**estilo, "bg": "#3a5a7d"})
        b_back.pack(side="left", padx=(8, 0))
        self._compacto_lbl = lbl
        self._compacto_btns = {"play": b_play, "pp": b_pp,
                               "stop": b_stop, "fan": b_fan,
                               "back": b_back}

        # ---- 2ª fila: lista de canciones JUNTO A la velocidad -----------
        cuerpo = tk.Frame(win, bg=fondo)
        cuerpo.pack(fill="x", padx=(7, 7), pady=(0, 6))

        marco_lb = tk.Frame(cuerpo, bg=fondo)
        marco_lb.pack(side="left", fill="both", expand=True)
        lb = tk.Listbox(
            marco_lb, height=6, width=20,
            bg=self.colores.get("Fondo de listas", "#1e1e1e"),
            fg=self.colores.get("Texto de listas", "#e8e8e8"),
            selectbackground=self.colores.get("Selección", "#4a6da7"),
            font=("Segoe UI", 9), activestyle="none",
            exportselection=False,   # no le borra la selección a la lista grande
            highlightthickness=0, relief="flat")
        scr = tk.Scrollbar(marco_lb, command=lb.yview, width=10)
        lb.config(yscrollcommand=scr.set)
        scr.pack(side="right", fill="y")
        lb.pack(side="left", fill="both", expand=True)
        lb.bind("<<ListboxSelect>>", self._compacto_elegir)
        self._compacto_lista = lb

        col = tk.Frame(cuerpo, bg=fondo)
        col.pack(side="right", padx=(8, 0))
        tk.Label(col, text="⏩ Velocidad", bg=fondo, fg=acento,
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")
        fila_v = tk.Frame(col, bg=fondo)
        fila_v.pack(fill="x", pady=(2, 0))
        estilo_v = dict(width=2, relief="flat", bg="#5f3f1e", fg="#ffe9c9",
                        font=("Segoe UI", 9, "bold"))
        tk.Button(fila_v, text="−",
                  command=lambda: self._compacto_vel(-0.25),
                  **estilo_v).pack(side="left", padx=1)
        lbl_v = tk.Label(fila_v, text="1.00x", bg=fondo, fg="#ffffff",
                         font=("Segoe UI", 9, "bold"), width=6)
        lbl_v.pack(side="left")
        tk.Button(fila_v, text="+",
                  command=lambda: self._compacto_vel(0.25),
                  **estilo_v).pack(side="left", padx=1)
        # el slider es la MISMA variable que la app: cambia al instante
        # (aunque suene) y se guarda con la canción
        tk.Scale(col, from_=0.1, to=20.0, resolution=0.1,
                 orient="horizontal", variable=self.speed_var, showvalue=0,
                 length=150, bg=fondo,
                 fg=self.colores.get("Texto secundario", "#cccccc"),
                 troughcolor=self.colores.get("Fondo de listas", "#1e1e1e"),
                 activebackground="#ffe066", highlightthickness=0,
                 sliderrelief="flat").pack(fill="x", pady=(2, 0))
        self._compacto_vel_lbl = lbl_v
        self._compacto_refrescar_lista()

        # arrastrar la barra desde cualquier punto (los botones igual clican)
        def _arrastra(e):
            try:
                nx, ny = e.x_root - win._dx, e.y_root - win._dy
                win.geometry("+%d+%d" % (nx, ny))
                # actualizar el rect del 👻 fantasma (mismo tamaño)
                if self._compacto_rect:
                    w, h = self._compacto_rect[2], self._compacto_rect[3]
                else:
                    w, h = win.winfo_reqwidth(), win.winfo_reqheight()
                self._compacto_rect = (nx, ny, w, h)
            except Exception:
                pass

        def _arranca(e):
            win._dx, win._dy = e.x, e.y

        win.bind("<ButtonPress-1>", _arranca)
        win.bind("<B1-Motion>", _arrastra)
        win.bind("<Escape>", lambda e: self._compacto_cerrar())

        # arriba a la derecha de la pantalla (donde no tapa el juego)
        win.update_idletasks()
        px = max(win.winfo_screenwidth() - win.winfo_reqwidth() - 14, 0)
        win.geometry("+%d+%d" % (px, 14))
        win.update_idletasks()
        # rect para el 👻 fantasma (saber si el mouse está cerca)
        self._compacto_rect = (px, 14, win.winfo_reqwidth(),
                               win.winfo_reqheight())
        self._compacto_oculta = False
        win.focus_force()
        self.root.withdraw()                 # la grande queda oculta
        self._compacto_poll()

    def _compacto_poll(self):
        """Mantiene la barrita al día: canción, progreso y botones."""
        win = getattr(self, "_compacto", None)
        if win is None:
            return
        try:
            if not win.winfo_exists():
                self._compacto = None
                return
        except Exception:
            self._compacto = None
            return
        try:
            canc = self._score_actual or "Sin canción"
            if len(canc) > 24:
                canc = canc[:23] + "…"
            if self.playing:
                total = len(self.groups)
                estado = "⏸ Pausado" if self.paused else "▶ Tocando"
                if total:
                    estado += "  %d/%d" % (min(self.pos, total), total)
            else:
                estado = "⏹ Listo"
            self._compacto_lbl.config(text="%s  ·  %s" % (canc, estado))
            b = self._compacto_btns
            b["play"].config(state="disabled" if self.playing else "normal")
            b["pp"].config(state="normal" if self.playing else "disabled",
                           text="▶" if self.paused else "⏸")
            b["stop"].config(state="normal" if self.playing else "disabled")
            if self._compacto_vel_lbl is not None:
                self._compacto_vel_lbl.config(text="%.2fx" % self.speed)
            # 👻 fantasma: botón encendido/apagado + auto-ocultamiento
            fan_on = bool(self.settings.get("compacto_fantasma"))
            b["fan"].config(bg="#7a5a9d" if fan_on else "#5f3f1e",
                            fg="#ffffff")
            if fan_on:
                self._compacto_fantasma_paso()
        except Exception:
            pass
        win.after(200, self._compacto_poll)

    def _compacto_cerrar(self):
        """Cierra la barra y vuelve a mostrar la ventana grande."""
        win = getattr(self, "_compacto", None)
        self._compacto = None
        self._compacto_lista = None
        self._compacto_vel_lbl = None
        self._compacto_rect = None
        self._compacto_oculta = False
        if win is not None:
            try:
                win.destroy()
            except Exception:
                pass
        try:
            self.root.deiconify()
            self.root.lift()
        except Exception:
            pass

    def _compacto_ocultar_transmision(self, win):
        """Le pide a Windows que NO muestre la barra en capturas de
        pantalla: al compartir pantalla (Discord, Zoom, Teams, OBS, Xbox
        Game Bar) la barrita no aparece (o sale negra), así transmitís sin
        que se vea tu control. Usa WDA_EXCLUDEFROMCAPTURE (Windows 10
        2004+) y como respaldo WDA_MONITOR (ventana negra en capturas).
        Devuelve True si Windows lo aceptó."""
        try:
            import ctypes
            from ctypes import wintypes
            u32 = ctypes.windll.user32
            u32.GetAncestor.argtypes = (wintypes.HWND, wintypes.UINT)
            u32.GetAncestor.restype = wintypes.HWND
            u32.SetWindowDisplayAffinity.argtypes = (wintypes.HWND,
                                                     wintypes.DWORD)
            u32.SetWindowDisplayAffinity.restype = wintypes.BOOL
            GA_ROOT = 2        # la ventana de primer nivel que la contiene
            hwnd = u32.GetAncestor(int(win.winfo_id()), GA_ROOT)
            if not hwnd:
                return False
            for afin in (0x11, 0x01):   # 0x11 invisible · 0x01 negra
                if u32.SetWindowDisplayAffinity(hwnd, afin):
                    return True
        except Exception:
            pass
        return False

    def _compacto_toggle_fantasma(self):
        """👻 Modo fantasma ON/OFF: con ON, la barra se OCULTA sola
        cuando el mouse no está cerca (Discord y otras apps de captura
        ignoran lo que pide Windows, así que la solución segura es que
        la barra no esté ahí). El estado se guarda para siempre."""
        nuevo = not bool(self.settings.get("compacto_fantasma"))
        self.settings["compacto_fantasma"] = nuevo
        self._save_settings_quiet()
        if not nuevo and getattr(self, "_compacto", None) is not None:
            try:
                self._compacto.deiconify()
                self._compacto_oculta = False
            except Exception:
                pass

    def _compacto_fantasma_paso(self):
        """👻 El mouse está cerca de la barra → se muestra; se fue →
        desaparece (60 px de margen alrededor para que aparezca antes
        de llegar). Así la barra nunca queda a la vista en un stream."""
        win = getattr(self, "_compacto", None)
        rect = getattr(self, "_compacto_rect", None)
        if win is None or not rect:
            return
        pos = _posicion_mouse()
        if pos is None:
            return
        px, py = pos
        x, y, w, h = rect
        cerca = (x - 60 <= px <= x + w + 60 and y - 60 <= py <= y + h + 60)
        oculta = getattr(self, "_compacto_oculta", False)
        try:
            if cerca and oculta:
                win.deiconify()
                self._compacto_oculta = False
            elif not cerca and not oculta:
                win.withdraw()
                self._compacto_oculta = True
        except Exception:
            pass

    def _velocidad_paso(self, subir):
        """Teclas globales , y .: suben/bajan la velocidad de a 0.1
        (1.00 → 1.10 → 1.20…), incluso con Roblox en primer plano y
        mientras la canción suena (la próxima nota ya va al nuevo ritmo).
        Va por speed_var: también se guarda con la canción."""
        try:
            v = float(self.speed_var.get())
        except (ValueError, tk.TclError):
            v = 1.0
        v = round(v + (0.1 if subir else -0.1), 2)
        self.speed_var.set(min(max(v, 0.1), 20.0))
        if self.playing:
            self.lbl_estado.config(
                text=f"⏩ Velocidad {self.speed:.2f}x en vivo")

    def _foreground_es_nuestro(self):
        """¿La ventana de primer plano es la de la app?"""
        try:
            import ctypes
            u32 = ctypes.windll.user32
            fg = u32.GetForegroundWindow()
            raiz = u32.GetAncestor(int(self.root.winfo_id()), 2)  # GA_ROOT
            return bool(fg) and fg == raiz
        except Exception:
            return False

    def _atajo_velocidad_responde(self):
        """¿Las teclas , y . deben tocar la velocidad AHORA? Con Roblox
        (u otra ventana) en primer plano: sí. Con la app en primer plano,
        solo si NO se está escribiendo en un campo de texto — así tipear
        una coma en el buscador o en un nombre no mueve la velocidad."""
        if not self._foreground_es_nuestro():
            return True
        try:
            w = self.root.focus_get()
        except Exception:
            return True
        return not isinstance(w, (tk.Entry, tk.Text, tk.Spinbox))

    def _tecla_global(self, key):
        """Teclas del listener global (funcionan con Roblox en primer
        plano): F8/F6/F7 para la reproducción y , / . para la velocidad.
        La app solo ESCUCHA la tecla: nunca la roba ni la reenvía."""
        try:
            if key == pkb.Key.f8:
                self._ui(self.start_play)
                return
            if key == pkb.Key.f6:
                self._ui(self.toggle_pause)
                return
            if key == pkb.Key.f7:
                self._ui(self.stop_play)
                return
            ch = getattr(key, "char", None)
            if ch in (",", ".") and self._atajo_velocidad_responde():
                self._ui(self._velocidad_paso, ch == ",")  # , sube · . baja
        except Exception:
            pass

    def _compacto_vel(self, delta):
        """−/+ de velocidad de la barrita (mismo paso que las teclas + y -:
        0.25). Va por speed_var, así cambia EN VIVO mientras suena y se
        guarda con la canción seleccionada, igual que en la app grande."""
        try:
            v = float(self.speed_var.get())
        except (ValueError, tk.TclError):
            v = 1.0
        self.speed_var.set(round(min(max(v + delta, 0.1), 20.0), 2))

    def _compacto_refrescar_lista(self, visibles=None):
        """Llena la listita de la barra con lo mismo que muestra la lista
        principal (mismo filtro de búsqueda y de carpeta)."""
        lb = getattr(self, "_compacto_lista", None)
        if lb is None:
            return
        if visibles is None:
            try:
                visibles = list(self.listbox.get(0, "end"))
            except Exception:
                visibles = []
        lb.delete(0, "end")
        for name in visibles:
            lb.insert("end", name)
        self._compacto_sincronizar()

    def _compacto_sincronizar(self):
        """Marca en la listita la canción que está activa en la app."""
        lb = getattr(self, "_compacto_lista", None)
        if lb is None:
            return
        act = getattr(self, "_score_actual", None)
        try:
            items = list(lb.get(0, "end"))
        except Exception:
            return
        lb.selection_clear(0, "end")
        if act in items:
            idx = items.index(act)
            lb.selection_set(idx)
            lb.activate(idx)
            lb.see(idx)

    def _compacto_elegir(self, _evt=None):
        """Clic en la listita de la barra: carga esa canción en la app
        (igual que si la eligieras en la lista grande)."""
        lb = getattr(self, "_compacto_lista", None)
        if lb is None:
            return
        sel = lb.curselection()
        if not sel:
            return
        name = lb.get(sel[0])
        try:
            items = list(self.listbox.get(0, "end"))
            if name not in items:
                return
            idx = items.index(name)
            self.listbox.selection_clear(0, "end")
            self.listbox.selection_set(idx)
            self.listbox.activate(idx)
            self._on_select_score()   # carga partitura + config de la canción
        except Exception:
            pass

    # ======================================================================
    # Teclas con auto-liberación (el hold nunca frena la canción)
    # ======================================================================
    def _cancel_held(self, base):
        """Suelta una tecla FÍSICA y cancela su timer de auto-liberación."""
        t = self._held.pop(base, None)
        if t is not None:
            t.cancel()
        try:
            self.key_ctrl.release(base)
        except Exception:
            pass

    def _shift_up(self):
        """Suelta el Shift del toque temporal (lo llama el timer)."""
        self._shift_timer = None
        if self._shift_down:
            self._shift_down = False
            try:
                self.key_ctrl.release(pkb.Key.shift)
            except Exception:
                pass

    def _press_key_hold(self, k, hold_s):
        """Presiona k y programa su suelta en hold_s segundos. Si ya estaba
        presionada, la suelta y vuelve a presionar (re-golpe fijo: las
        repeticiones SIEMPRE se escuchan).

        Todo el registro (_held) va por TECLA FÍSICA: así '1' y '!'
        (ambos tocan la tecla 1) o 's' y 'S' no se pisan entre sí — antes,
        si una estaba sostenida, la otra la pisaba y el juego dejaba de
        escuchar las notas siguientes.

        Las notas con Shift (mayúsculas, ! @ # $ % ^ & * ( )) reciben un
        TOQUE de Shift solo en su instante: Shift↓ → tecla↓ → (margen) →
        Shift↑. El toque dura ~35% de la separación entre notas: suficiente
        para que el juego lo registre, sin contaminar las demás teclas."""
        base, con_shift = _note_to_key(k)
        # margen que el Shift queda presionado: suficiente para que el juego
        # lo registre (algunos juegos leen el teclado por frames), pero mucho
        # menor que la separación entre notas (así no contamina las demás)
        margen = min(0.05, max(0.012, (self.base_gap / max(self.speed, 0.1)) * 0.35))
        if base in self._held:
            # SIEMPRE re-golpear (fijo): suelta y vuelve a presionar, con
            # pausa ENTRE la suelta y el nuevo golpe — si es más corta que
            # un frame del juego (~16 ms), Roblox no registra ni la suelta
            # ni el re-golpe y la repetición "no suena". Con ~40 ms el
            # juego ve claramente suelta -> golpe nuevo.
            self._cancel_held(base)
            re_gap = max(0.02, min(0.045, margen))
            time.sleep(re_gap)
        try:
            if con_shift:
                if self._shift_timer is not None:
                    self._shift_timer.cancel()
                    self._shift_timer = None
                if not self._shift_down:      # solo 1 Shift por ráfaga
                    self.key_ctrl.press(pkb.Key.shift)
                    self._shift_down = True
                self.key_ctrl.press(base)
                self._shift_timer = threading.Timer(margen, self._shift_up)
                self._shift_timer.daemon = True
                self._shift_timer.start()
            else:
                self.key_ctrl.press(base)
        except Exception:
            return
        holder = {}

        def fire():
            self._release_if_owner(base, holder["t"])

        t = threading.Timer(hold_s, fire)
        holder["t"] = t
        t.daemon = True
        self._held[base] = t
        t.start()

    def _release_if_owner(self, base, timer):
        """Solo suelta la tecla si este timer sigue siendo el dueño del
        estado actual (evita que un timer viejo corte una pulsación nueva)."""
        if self._held.get(base) is timer:
            self._held.pop(base, None)
            try:
                self.key_ctrl.release(base)
            except Exception:
                pass

    def _release_all_held(self):
        """Suelta todas las teclas pendientes (al detener o cerrar)."""
        if self._shift_timer is not None:
            self._shift_timer.cancel()
            self._shift_timer = None
        self._shift_down = False
        for base, t in list(self._held.items()):
            t.cancel()
            try:
                self.key_ctrl.release(base)
            except Exception:
                pass
        self._held.clear()
        try:
            self.key_ctrl.release(pkb.Key.shift)   # por si el Shift quedó apretado
        except Exception:
            pass

    # ======================================================================
    # Analizador de videos
    # ======================================================================
    def _analyze_video_dialog(self):
        if not _find_ytdlp():
            messagebox.showinfo(
                "Falta yt-dlp",
                "Para analizar videos se necesita 'yt-dlp'.\n\n"
                "Ejecuta en la terminal:\n\n    pip install yt-dlp")
            return

        win = tk.Toplevel(self.root)
        win.title("🎥 Analizar video")
        win.geometry("660x680")
        win.configure(bg="#2b2b2b")
        win.grab_set()

        results = []          # [{"title":..., "sheet":...}, ...]

        tk.Label(win, text="🎥 Analizar video", bg="#2b2b2b", fg="white",
                 font=("Segoe UI", 14, "bold")).pack(anchor="w", padx=12,
                                                     pady=(12, 2))
        tk.Label(win, text="Pega uno o más links (uno por línea):",
                 bg="#2b2b2b", fg="#cccccc", font=("Segoe UI", 10)
                 ).pack(anchor="w", padx=12)
        links = tk.Text(win, height=4, font=("Consolas", 11), bg="#1e1e1e",
                        fg="#e8e8e8", insertbackground="white")
        links.pack(fill="x", padx=12, pady=4)

        comments_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(win, text="Buscar también en los comentarios (más lento)",
                        variable=comments_var).pack(anchor="w", padx=12)

        trans_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(win, text="🎹 Transcribir el AUDIO del video "
                                  "(cualquier música/instrumento, experimental)",
                        variable=trans_var).pack(anchor="w", padx=12)

        status = tk.Label(win, text="Listo para analizar", bg="#2b2b2b",
                          fg="#9fe870", font=("Segoe UI", 10, "bold"),
                          wraplength=600, justify="left")
        status.pack(anchor="w", padx=12, pady=6)

        tk.Label(win, text="Resultados encontrados:", bg="#2b2b2b", fg="#cccccc",
                 font=("Segoe UI", 10)).pack(anchor="w", padx=12)
        results_box = tk.Listbox(win, height=5, bg="#1e1e1e", fg="#e8e8e8",
                                 selectbackground="#4a6da7", font=("Segoe UI", 10))
        results_box.pack(fill="x", padx=12, pady=2)

        tk.Label(win, text="Nombre de la partitura:", bg="#2b2b2b", fg="#cccccc",
                 font=("Segoe UI", 10)).pack(anchor="w", padx=12, pady=(6, 0))
        name_entry = tk.Entry(win, font=("Segoe UI", 11))
        name_entry.pack(fill="x", padx=12)

        tk.Label(win, text="Partitura encontrada (puedes editarla antes de guardar):",
                 bg="#2b2b2b", fg="#cccccc", font=("Segoe UI", 10)
                 ).pack(anchor="w", padx=12, pady=(6, 0))
        preview = tk.Text(win, height=10, font=("Consolas", 12), bg="#1e1e1e",
                          fg="#e8e8e8", insertbackground="white", wrap="word")
        preview.pack(fill="both", expand=True, padx=12, pady=4)

        def load_result(_evt=None):
            sel = results_box.curselection()
            if not sel:
                return
            r = results[sel[0]]
            name_entry.delete(0, "end")
            name_entry.insert(0, r["title"])
            preview.delete("1.0", "end")
            preview.insert("1.0", r["sheet"])

        results_box.bind("<<ListboxSelect>>", load_result)

        btn_row = tk.Frame(win, bg="#2b2b2b")
        btn_row.pack(fill="x", padx=12, pady=8)
        btn_analizar = tk.Button(btn_row, text="▶ Analizar links",
                                 bg="#3a5a7d", fg="white", relief="flat",
                                 font=("Segoe UI", 11, "bold"))
        btn_analizar.pack(side="left")

        def guardar():
            body = preview.get("1.0", "end").strip()
            if not parse_sheet(body):
                messagebox.showwarning("AutoPiano",
                                       "No hay notas válidas en la vista previa.",
                                       parent=win)
                return
            name = name_entry.get().strip() or "Video"
            base, i = name, 2
            while name in self.scores:
                name = f"{base} ({i})"
                i += 1
            self.scores[name] = body
            self._score_actual = name     # activa: su config va a ELLA
            self._asignar_seccion_nueva(name)
            self._save_scores()
            self._refresh_list(keep=name)
            self._set_board_text(body)
            status.config(text=f"💾 '{name}' guardada en la lista", fg="#9fe870")

        tk.Button(btn_row, text="💾 Guardar en la lista", command=guardar,
                  bg="#3a7d44", fg="white", relief="flat",
                  font=("Segoe UI", 11, "bold")).pack(side="right")

        def analizar():
            urls = [l.strip() for l in links.get("1.0", "end").splitlines()
                    if l.strip()]
            if not urls:
                status.config(text="⚠ Pega al menos un link", fg="#ffd7d7")
                return
            btn_analizar.config(state="disabled")
            use_comments = comments_var.get()

            def worker():
                res = []
                use_trans = trans_var.get()
                if use_trans and not _find_ffmpeg():
                    self._ui(status.config,
                             text="✖ Falta ffmpeg.exe junto a la app para "
                                  "transcribir audio", fg="#ffd7d7")

                for i, u in enumerate(urls, 1):
                    # --- modo transcripción de audio ------------------------
                    if use_trans and _find_ffmpeg():
                        try:
                            self._ui(status.config,
                                     text=f"⏳ Descargando audio {i}/{len(urls)}…",
                                     fg="#ffe066")
                            audio = _download_audio(u)
                            self._ui(status.config,
                                     text=f"⏳ Convirtiendo audio {i}/{len(urls)}…",
                                     fg="#ffe066")
                            wav = _to_wav_16k(audio)

                            def prog(p, i=i, n=len(urls)):
                                self._ui(status.config,
                                         text=f"🎹 Transcribiendo {i}/{n}… "
                                              f"{int(p * 100)}%",
                                         fg="#ffe066")

                            sheet = transcribe_audio(wav, progress=prog)
                            if sheet.strip():
                                res.append({"title": _video_title(u) + " (audio)",
                                            "sheet": sheet})
                                self._ui(status.config,
                                         text=f"✔ {i}/{len(urls)}: transcripción "
                                              f"lista", fg="#9fe870")
                            else:
                                self._ui(status.config,
                                         text=f"✖ {i}/{len(urls)}: no se detectaron "
                                              f"notas en el audio", fg="#ffd7d7")
                        except Exception as e:
                            self._ui(status.config,
                                     text=f"✖ Audio {u[:50]}: {e}", fg="#ffd7d7")

                    # --- extracción de texto (siempre) ----------------------
                    self._ui(status.config,
                             text=f"⏳ Analizando {i}/{len(urls)}… (descripción/"
                                  f"subtítulos)",
                             fg="#ffe066")
                    try:
                        title, blob = _fetch_video(u, use_comments)
                        cands = _extract_candidates(blob)
                        sheet = cands[0] if cands else blob[:4000]
                        if sheet.strip():
                            res.append({"title": title, "sheet": sheet.strip()})
                            self._ui(status.config,
                                     text=f"✔ {i}/{len(urls)}: {title[:70]}",
                                     fg="#9fe870")
                        else:
                            self._ui(status.config,
                                     text=f"✖ {i}/{len(urls)}: sin texto útil",
                                     fg="#ffd7d7")
                    except Exception as e:
                        self._ui(status.config,
                                 text=f"✖ Error en {u[:60]}: {e}", fg="#ffd7d7")

                def done():
                    btn_analizar.config(state="normal")
                    results[:] = res
                    results_box.delete(0, "end")
                    for r in res:
                        results_box.insert("end", r["title"])
                    if res:
                        results_box.selection_set(0)
                        load_result()
                        status.config(
                            text=f"✔ Listo ({len(res)} resultado(s)). Revisa, "
                                 f"edita y presiona 'Guardar en la lista'.",
                            fg="#9fe870")
                    else:
                        status.config(
                            text="✖ No se encontró ninguna partitura. Prueba "
                                 "activando los comentarios o con otro video.",
                            fg="#ffd7d7")

                self._ui(done)

            threading.Thread(target=worker, daemon=True).start()

        btn_analizar.config(command=analizar)

    # ======================================================================
    # Búsqueda de partituras en la web
    # ======================================================================
    def _buscar_notas_dialog(self):
        """🌐 Buscar notas en la web: escribís lo que querés (ej:
        "raining tacos roblox sheet"), se buscan páginas con partituras
        en DuckDuckGo, se muestran los resultados y cada uno se guarda
        directo con el nombre que elijas."""
        win = tk.Toplevel(self.root)
        win.title("🌐 Buscar notas en la web")
        win.geometry("720x690")
        win.configure(bg="#2b2b2b")
        win.grab_set()

        results = []          # [{"title", "sheet", "url"}, ...]

        tk.Label(win, text="🌐 Buscar notas en la web", bg="#2b2b2b",
                 fg="white", font=("Segoe UI", 14, "bold")).pack(
                     anchor="w", padx=12, pady=(12, 2))
        tk.Label(win, text='¿Qué partitura buscás?  ej: "raining tacos '
                           'roblox sheet"',
                 bg="#2b2b2b", fg="#cccccc",
                 font=("Segoe UI", 10)).pack(anchor="w", padx=12)

        fila = tk.Frame(win, bg="#2b2b2b")
        fila.pack(fill="x", padx=12, pady=4)
        query = tk.Entry(fila, font=("Segoe UI", 12))
        query.pack(side="left", fill="x", expand=True)
        btn_buscar = tk.Button(fila, text="🔍 Buscar", bg="#3a5a7d",
                               fg="white", relief="flat",
                               font=("Segoe UI", 11, "bold"))
        btn_buscar.pack(side="left", padx=(8, 0))
        query.bind("<Return>", lambda _e: btn_buscar.invoke())

        status = tk.Label(win, text="Escribí qué querés buscar y presioná "
                                    "🔍 Buscar",
                          bg="#2b2b2b", fg="#9fe870",
                          font=("Segoe UI", 10, "bold"),
                          wraplength=680, justify="left")
        status.pack(anchor="w", padx=12, pady=6)

        tk.Label(win, text="Resultados encontrados:", bg="#2b2b2b",
                 fg="#cccccc", font=("Segoe UI", 10)).pack(anchor="w",
                                                           padx=12)
        results_box = tk.Listbox(win, height=5, bg="#1e1e1e", fg="#e8e8e8",
                                 selectbackground="#4a6da7",
                                 exportselection=False,
                                 font=("Segoe UI", 10))
        results_box.pack(fill="x", padx=12, pady=2)

        tk.Label(win, text="Nombre de la partitura (el que quieras):",
                 bg="#2b2b2b", fg="#cccccc",
                 font=("Segoe UI", 10)).pack(anchor="w", padx=12,
                                             pady=(6, 0))
        name_entry = tk.Entry(win, font=("Segoe UI", 11))
        name_entry.pack(fill="x", padx=12)

        tk.Label(win, text="Partitura encontrada (podés editarla antes de "
                           "guardar):",
                 bg="#2b2b2b", fg="#cccccc", font=("Segoe UI", 10)
                 ).pack(anchor="w", padx=12, pady=(6, 0))
        preview = tk.Text(win, height=9, font=("Consolas", 12),
                          bg="#1e1e1e", fg="#e8e8e8",
                          insertbackground="white", wrap="word")
        preview.pack(fill="both", expand=True, padx=12, pady=4)

        def load_result(_evt=None):
            sel = results_box.curselection()
            if not sel:
                return
            r = results[sel[0]]
            name_entry.delete(0, "end")
            name_entry.insert(0, r["title"])
            preview.delete("1.0", "end")
            preview.insert("1.0", r["sheet"])

        results_box.bind("<<ListboxSelect>>", load_result)

        def guardar():
            body = preview.get("1.0", "end").strip()
            if not parse_sheet(body):
                messagebox.showwarning("AutoPiano",
                                       "No hay notas válidas en la vista "
                                       "previa.", parent=win)
                return
            name = name_entry.get().strip() or "Web"
            base, i = name, 2
            while name in self.scores:
                name = f"{base} ({i})"
                i += 1
            self.scores[name] = body
            self._score_actual = name      # activa: su config va a ELLA
            self._asignar_seccion_nueva(name)
            self._save_scores()
            self._refresh_list(keep=name)
            self._set_board_text(body)
            status.config(text=f"💾 '{name}' guardada en la lista",
                          fg="#9fe870")

        fila2 = tk.Frame(win, bg="#2b2b2b")
        fila2.pack(fill="x", padx=12, pady=8)
        tk.Button(fila2, text="💾 Guardar en la lista", command=guardar,
                  bg="#3a7d44", fg="white", relief="flat",
                  font=("Segoe UI", 11, "bold")).pack(side="right")

        def buscar():
            q = query.get().strip()
            if not q:
                status.config(text="⚠ Escribí qué partitura buscás",
                              fg="#ffd7d7")
                return
            btn_buscar.config(state="disabled")
            status.config(text="⏳ Buscando en la web…", fg="#ffe066")

            def avance(txt):
                self._ui(status.config, text=txt, fg="#ffe066")

            def worker():
                try:
                    res = _web_buscar_partituras(q, avance=avance)
                except Exception as e:
                    def fallo(e=e):
                        btn_buscar.config(state="normal")
                        status.config(text=f"✖ No se pudo buscar: {e}",
                                      fg="#ffd7d7")
                    self._ui(fallo)
                    return

                def done(res=res):
                    btn_buscar.config(state="normal")
                    results[:] = res
                    results_box.delete(0, "end")
                    for r in res:
                        results_box.insert("end", r["title"])
                    if res:
                        results_box.selection_set(0)
                        load_result()
                        status.config(
                            text=f"✔ {len(res)} resultado(s). Elegí uno, "
                                 f"poné el nombre que quieras y guardá.",
                            fg="#9fe870")
                    else:
                        status.config(
                            text="✖ No se encontró ninguna partitura. "
                                 "Probá con otras palabras.",
                            fg="#ffd7d7")

                self._ui(done)

            threading.Thread(target=worker, daemon=True).start()

        btn_buscar.config(command=buscar)
        query.focus_set()

    # ======================================================================
    # v4.23 — Diálogos: 📈 Récords, ☁️ Mi nube, 🌍 Comunidad
    # ======================================================================
    def _records_dialog(self):
        """📈 Récords por canción: cuántas veces la tocaste, cuántas la
        terminaste bien, la mayor velocidad lograda y la racha de días."""
        win = tk.Toplevel(self.root)
        win.title("📈 Récords y racha")
        win.geometry("520x520")
        win.configure(bg="#2b2b2b")
        win.grab_set()

        racha = self.records.get("racha", {})
        tk.Label(win, text="📈 Récords y racha", bg="#2b2b2b", fg="white",
                 font=("Segoe UI", 14, "bold")).pack(anchor="w", padx=12,
                                                     pady=(12, 2))
        tk.Label(win,
                 text=f"🔥 Racha: {int(racha.get('dias', 0) or 0)} día(s) "
                      f"seguidos tocando\n(toqué hoy para mantenerla)",
                 bg="#2b2b2b", fg="#ff9f6b", font=("Segoe UI", 11),
                 justify="left").pack(anchor="w", padx=12)

        marco = tk.Frame(win, bg="#1e1e1e")
        marco.pack(fill="both", expand=True, padx=12, pady=8)
        cols = ("Canción", "Tocadas", "OK", "Máx. vel")
        tree = ttk.Treeview(marco, columns=cols, show="headings",
                            height=14)
        for c, w in zip(cols, (230, 70, 55, 80)):
            tree.heading(c, text=c)
            tree.column(c, width=w, anchor="w")
        scroll = ttk.Scrollbar(marco, orient="vertical",
                               command=tree.yview)
        tree.configure(yscrollcommand=scroll.set)
        tree.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

        canc = self.records.get("canciones", {})

        def refrescar():
            tree.delete(*tree.get_children())
            for nombre in sorted(canc):
                fila = canc[nombre] if isinstance(canc[nombre], dict) else {}
                tree.insert("", "end", values=(
                    nombre,
                    int(fila.get("tocadas", 0) or 0),
                    int(fila.get("completadas", 0) or 0),
                    f"{float(fila.get('mejor_vel', 0) or 0):.2f}x"))
        refrescar()

        def abrir(_evt=None):
            sel = tree.selection()
            if sel and sel[0] in self.scores:
                self.listbox.selection_clear(0, "end")
                try:
                    idx = list(self.scores.keys()).index(sel[0])
                    self.listbox.selection_set(idx)
                except (ValueError, tk.TclError):
                    pass
                self._on_select_score()
                win.destroy()

        tree.bind("<Double-1>", abrir)

        fila = tk.Frame(win, bg="#2b2b2b")
        fila.pack(fill="x", padx=12, pady=(0, 12))
        tk.Button(fila, text="Abrir canción (doble clic)",
                  command=abrir, bg="#3a5a7d", fg="white",
                  relief="flat").pack(side="left")
        tk.Button(fila, text="Cerrar", command=win.destroy,
                  bg="#555555", fg="white", relief="flat"
                  ).pack(side="right")

    def _nube_dialog(self):
        """☁️ Mi nube: respaldo/restore de mis partituras en un lugar
        privado de mi cuenta de GitHub (gist)."""
        win = tk.Toplevel(self.root)
        win.title("☁️ Mi nube de partituras")
        win.geometry("560x470")
        win.configure(bg="#2b2b2b")
        win.grab_set()

        tk.Label(win, text="☁️ Mi nube de partituras", bg="#2b2b2b",
                 fg="white", font=("Segoe UI", 14, "bold")
                 ).pack(anchor="w", padx=12, pady=(12, 2))
        info = tk.Label(
            win, justify="left", bg="#2b2b2b", fg="#cccccc",
            font=("Segoe UI", 10),
            text="Guardá tus partituras y ajustes en un lugar PRIVADO de\n"
                 "tu cuenta de GitHub. En otra PC con AutoPiano, entrás a\n"
                 "esta misma pantalla y das ▼ Restaurar: tenés todo al\n"
                 "instante. Nunca se borra nada solo.")
        info.pack(anchor="w", padx=12)

        tiene_token = bool(_gh_token())
        estado = tk.Label(
            win,
            text=("✔ Cuenta detectada: se puede usar la nube"
                  if tiene_token else
                  "⚠ No se encontró tu cuenta de GitHub en esta PC.\n"
                  "La nube usa el token de gh CLI (si iniciaste sesión)."),
            bg="#2b2b2b", fg="#9fe870" if tiene_token else "#ffe066",
            font=("Segoe UI", 10, "bold"), justify="left",
            wraplength=520)
        estado.pack(anchor="w", padx=12, pady=8)

        log = tk.Text(win, height=10, bg="#1e1e1e", fg="#e8e8e8",
                      font=("Consolas", 10), state="disabled",
                      wrap="word")
        log.pack(fill="both", expand=True, padx=12, pady=4)

        def decir(txt, color="#e8e8e8"):
            log.config(state="normal")
            log.insert("end", txt + "\n")
            log.tag_add("c", "end-2c", "end-1c")
            log.tag_config("c", foreground=color)
            log.see("end")
            log.config(state="disabled")

        def en_hilo(fn, etiqueta):
            btns.config(state="disabled")
            decir(f"⏳ {etiqueta}…", "#ffe066")

            def worker():
                try:
                    res = fn()
                except Exception as e:
                    res = f"error: {e}"

                def done(res=res):
                    mensajes = {
                        "ok": ("✔ Listo", "#9fe870"),
                        "sin-token": ("✖ No encontré tu token de GitHub "
                                      "en esta PC.", "#ffd7d7"),
                        "sin-gist": ("✖ No pude crear/abrir el respaldo "
                                     "en la nube.", "#ffd7d7"),
                        "vacio": ("⚠ El respaldo de la nube está vacío "
                                  "(nada que restaurar).", "#ffe066"),
                        "error": ("✖ Error de red o de GitHub. Revisá tu "
                                  "internet.", "#ffd7d7"),
                    }
                    texto, color = mensajes.get(
                        res, (f"Resultado: {res}", "#e8e8e8"))
                    decir(texto, color)
                    if res == "ok" and etiqueta.startswith("Bajar"):
                        decir("🔄 Cerrá y volvé a abrir la app para ver "
                              "las partituras restauradas.", "#ffe066")
                    btns.config(state="normal")
                self._ui(done)

            threading.Thread(target=worker, daemon=True).start()

        btns = tk.Frame(win, bg="#2b2b2b")
        btns.pack(fill="x", padx=12, pady=8)
        tk.Button(btns, text="⬆️ Subir mis partituras",
                  command=lambda: en_hilo(nube_subir, "Subir"),
                  bg="#3a7d44", fg="white", relief="flat",
                  font=("Segoe UI", 11, "bold")).pack(
                      side="left", expand=True, fill="x", padx=(0, 4))
        tk.Button(btns, text="⬇️ Restaurar desde la nube",
                  command=lambda: en_hilo(nube_bajar, "Bajar"),
                  bg="#3d5a80", fg="white", relief="flat",
                  font=("Segoe UI", 11, "bold")).pack(
                      side="left", expand=True, fill="x", padx=(4, 0))

        decir("Listo para usar." if tiene_token
              else "La nube necesita que en esta PC hayas iniciado sesión "
                   "con gh CLI (una sola vez).")

    def _comunidad_dialog(self):
        """🌍 Canciones de la comunidad: catálogo compartido en el repo
        oficial — bajar las de otros o subir las tuyas."""
        win = tk.Toplevel(self.root)
        win.title("🌍 Canciones de la comunidad")
        win.geometry("640x560")
        win.configure(bg="#2b2b2b")
        win.grab_set()

        tk.Label(win, text="🌍 Canciones de la comunidad", bg="#2b2b2b",
                 fg="white", font=("Segoe UI", 14, "bold")
                 ).pack(anchor="w", padx=12, pady=(12, 2))
        status = tk.Label(win, text="⏳ Cargando el catálogo…",
                          bg="#2b2b2b", fg="#ffe066",
                          font=("Segoe UI", 10, "bold"))
        status.pack(anchor="w", padx=12)

        lista = []           # [(nombre, download_url)]

        listbox = tk.Listbox(win, height=12, bg="#1e1e1e", fg="#e8e8e8",
                             selectbackground="#4a6da7",
                             exportselection=False,
                             font=("Segoe UI", 11))
        listbox.pack(fill="x", padx=12, pady=4)

        preview = tk.Text(win, height=8, bg="#1e1e1e", fg="#e8e8e8",
                          font=("Consolas", 11), state="disabled",
                          wrap="word")
        preview.pack(fill="both", expand=True, padx=12, pady=4)

        def ver(_evt=None):
            sel = listbox.curselection()
            if not sel:
                return
            nombre, url = lista[sel[0]]
            status.config(text=f"⏳ Descargando '{nombre}'…", fg="#ffe066")

            def worker(nombre=nombre, url=url):
                texto = comunidad_leer(url)

                def done(texto=texto):
                    preview.config(state="normal")
                    preview.delete("1.0", "end")
                    preview.insert("1.0", texto or "(no se pudo descargar)")
                    preview.config(state="disabled")
                    if texto:
                        status.config(
                            text=f"✔ '{nombre}' — la podés guardar con "
                                 f"⬇️ Guardar en mi lista",
                            fg="#9fe870")
                    else:
                        status.config(text=f"✖ No se pudo descargar "
                                           f"'{nombre}'.", fg="#ffd7d7")
                self._ui(done)
            threading.Thread(target=worker, daemon=True).start()

        listbox.bind("<<ListboxSelect>>", ver)

        def guardar():
            sel = listbox.curselection()
            if not sel:
                messagebox.showinfo("Comunidad", "Elegí una canción "
                                    "de la lista.", parent=win)
                return
            cuerpo = preview.get("1.0", "end").strip()
            if not cuerpo or cuerpo.startswith("(no se pudo"):
                return
            nombre = lista[sel[0]][0].rsplit(".", 1)[0]
            base, i = nombre, 2
            while nombre in self.scores:
                nombre = f"{base} ({i})"
                i += 1
            self.scores[nombre] = cuerpo
            self._score_actual = nombre
            self._asignar_seccion_nueva(nombre)
            self._save_scores()
            self._refresh_list(keep=nombre)
            status.config(text=f"💾 '{nombre}' guardada en tu lista",
                          fg="#9fe870")

        def subir():
            actual = self._current_score_name()
            if not actual:
                messagebox.showinfo("Comunidad", "Elegí primero una "
                                    "canción TUYA en la lista de la app.",
                                    parent=win)
                return
            if not messagebox.askyesno(
                    "Comunidad",
                    f"¿Subir '{actual}' a la carpeta pública de la "
                    f"comunidad?\n\nTodos podrán verla y bajarla con tu "
                    f"nombre de usuario.", parent=win):
                return
            status.config(text=f"⏳ Subiendo '{actual}'…", fg="#ffe066")
            texto = self.scores.get(actual, "")

            def worker(actual=actual, texto=texto):
                res = comunidad_subir(actual, texto)

                def done(res=res):
                    mensajes = {"ok": "✔ ¡Subida! Ya está en el catálogo "
                                      "de la comunidad.",
                                "sin-token": "✖ Sin token de GitHub en "
                                             "esta PC (sólo el dueño del "
                                             "repo puede subir).",
                                "error": "✖ No se pudo subir (red o "
                                         "permisos)."}
                    color = "#9fe870" if res == "ok" else "#ffd7d7"
                    status.config(text=mensajes.get(res, f"Resultado: {res}"),
                                  fg=color)
                    if res == "ok":
                        cargar()
                self._ui(done)
            threading.Thread(target=worker, daemon=True).start()

        def cargar():
            status.config(text="⏳ Cargando el catálogo…", fg="#ffe066")

            def worker():
                try:
                    res = comunidad_listar()
                except Exception:
                    res = []

                def done(res=res):
                    lista[:] = res
                    listbox.delete(0, "end")
                    for nombre, _url in res:
                        listbox.insert("end", nombre)
                    if res:
                        status.config(
                            text=f"✔ {len(res)} canción(es) en el "
                                 f"catálogo. Elegí una para verla.",
                            fg="#9fe870")
                    else:
                        status.config(
                            text="✖ El catálogo está vacío o no hay "
                                 "internet.", fg="#ffe066")
                self._ui(done)
            threading.Thread(target=worker, daemon=True).start()

        fila = tk.Frame(win, bg="#2b2b2b")
        fila.pack(fill="x", padx=12, pady=(4, 12))
        tk.Button(fila, text="🔄 Actualizar", command=cargar,
                  bg="#555555", fg="white", relief="flat").pack(side="left")
        tk.Button(fila, text="⬇️ Guardar en mi lista", command=guardar,
                  bg="#3a7d44", fg="white", relief="flat",
                  font=("Segoe UI", 10, "bold")).pack(side="right",
                                                      padx=6)
        tk.Button(fila, text="📤 Subir la mía", command=subir,
                  bg="#6b4a2b", fg="white", relief="flat",
                  font=("Segoe UI", 10, "bold")).pack(side="right")

        cargar()

    # ======================================================================
    # Exportar a .txt / respaldo / eliminar
    # ======================================================================
    def _export_txt(self):
        """Guarda la partitura seleccionada como archivo .txt (para compartir)."""
        name = self._current_score_name()
        if not name:
            messagebox.showinfo("AutoPiano",
                                "Selecciona una partitura de la lista para exportar.")
            return
        # vaciar el auto-guardado pendiente para exportar la última edición
        if self._dirty and self._autosave_id:
            self.root.after_cancel(self._autosave_id)
            self._autosave_id = None
            self._autosave_board()
        body = self.scores.get(name, "")
        path = filedialog.asksaveasfilename(
            title=f"Exportar '{name}'",
            defaultextension=".txt",
            initialfile=f"{name}.txt",
            filetypes=[("Archivos de texto", "*.txt"), ("Todos", "*.*")])
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(body)
            self.lbl_estado.config(text=f"📤 Exportada a {os.path.basename(path)}")
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo guardar el archivo:\n{e}")

    def _backup_all(self):
        """Guarda TODAS las partituras + los ajustes en un solo archivo."""
        path = filedialog.asksaveasfilename(
            title="Guardar respaldo (partituras + ajustes)",
            defaultextension=".json",
            initialfile="autopiano_respaldo.json",
            filetypes=[("Respaldo AutoPiano", "*.json")])
        if not path:
            return
        datos = {
            "app": "AutoPiano",
            "scores": dict(self.scores),
            "settings": {k: v for k, v in self.settings.items()
                         if not k.startswith("last_")},
            # la configuración personalizada de cada canción viaja con ellas
            "song_settings": {k: dict(v) for k, v in self._song_overrides.items()
                              if k in self.scores},
            # y las secciones (carpetas) con sus asignaciones
            "secciones": {"secciones": list(self.secciones),
                          "asignaciones": dict(self.seccion_de)},
            # y la paleta de colores personalizada (si cambió algo)
            "colores": dict(self.colores),
        }
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(datos, f, ensure_ascii=False, indent=2)
            self.lbl_estado.config(
                text=f"💾 Respaldo: {len(self.scores)} partituras → "
                     f"{os.path.basename(path)}")
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo crear el respaldo:\n{e}")

    def _restore_backup(self):
        """Recupera partituras y ajustes desde un archivo de respaldo."""
        path = filedialog.askopenfilename(
            title="Elegir archivo de respaldo",
            filetypes=[("Respaldo AutoPiano", "*.json"), ("Todos", "*.*")])
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8-sig") as f:
                datos = json.load(f)
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo leer el respaldo:\n{e}")
            return
        scores = datos.get("scores")
        if not isinstance(scores, dict):
            messagebox.showwarning("AutoPiano",
                                   "Ese archivo no es un respaldo de AutoPiano.")
            return
        for nombre, cuerpo in scores.items():
            if isinstance(nombre, str) and isinstance(cuerpo, str):
                self.scores[nombre] = cuerpo
        self._save_scores()
        ajustes = datos.get("settings")
        if isinstance(ajustes, dict):
            for k, v in ajustes.items():
                if k in DEFAULT_SETTINGS:
                    self.settings[k] = v
            self._save_settings()
            self._apply_settings()
        # configuración personalizada de cada canción (respaldos nuevos);
        # los respaldos viejos no la traen y no se pierde nada por eso
        song = datos.get("song_settings")
        if isinstance(song, dict):
            self._song_overrides = {k: dict(v) for k, v in song.items()
                                    if isinstance(v, dict) and k in self.scores}
            self._guardar_song_settings()
        # paleta de colores del respaldo, si trae (los viejos no traen)
        col_datos = datos.get("colores")
        if isinstance(col_datos, dict):
            validos = {k: v for k, v in col_datos.items()
                       if k in COLORES_DEFAULT and self._hex_valido(str(v))}
            if validos:
                self.colores.update(validos)
                self._guardar_colores()
                self._aplicar_colores()
        # secciones (carpetas) del respaldo, si trae (los viejos no traen).
        # Se FUSIONAN con las actuales: las del respaldo primero y las que
        # ya existían acá detrás, así ninguna asignación queda huérfana
        sec_datos = datos.get("secciones")
        if isinstance(sec_datos, dict):
            secs = sec_datos.get("secciones")
            if isinstance(secs, list):
                vistas = ["General"]
                for s in list(secs) + self.secciones:
                    if isinstance(s, str) and s.strip() and s.strip() not in vistas:
                        vistas.append(s.strip())
                self.secciones = vistas
            asig = sec_datos.get("asignaciones")
            if isinstance(asig, dict):
                for k, v in asig.items():
                    if (isinstance(k, str) and isinstance(v, str)
                            and v in self.secciones and k in self.scores):
                        self.seccion_de[k] = v
            self._guardar_secciones()
            self._refrescar_combo_secciones()
        # conservar la selección actual si sigue existiendo
        actual = getattr(self, "_score_actual", None)
        self._refresh_list(keep=actual if actual in self.scores else None)
        if actual not in self.scores:
            self._score_actual = None
            self._set_board_text("")
        self._aplicar_song_overrides()
        self.lbl_estado.config(
            text=f"📥 Restauradas {len(scores)} partituras desde el respaldo")

    def _delete_score(self):
        sel = list(self.listbox.curselection())
        nombres = [self.listbox.get(i) for i in sel
                   if 0 <= i < self.listbox.size()]
        if not nombres:
            return
        if len(nombres) == 1:
            msg = f"¿Eliminar '{nombres[0]}'?"
        else:
            msg = (f"¿Eliminar {len(nombres)} canciones?\n\n"
                   + "\n".join(nombres[:10])
                   + ("\n..." if len(nombres) > 10 else ""))
        if messagebox.askyesno("Eliminar", msg):
            if self.playing:
                self.stop_play()
            for name in nombres:
                self.scores.pop(name, None)
                # su configuración personalizada ya no sirve: fuera
                if name in self._song_overrides:
                    del self._song_overrides[name]
                # ídem su asignación de sección
                if name in self.seccion_de:
                    del self.seccion_de[name]
                if getattr(self, "_score_actual", None) == name:
                    self._score_actual = None
            self._save_scores()
            self._guardar_song_settings()
            self._guardar_secciones()
            self._refresh_list()
            self._set_board_text("")

    # ======================================================================
    # Utilidades
    # ======================================================================
    def _ui(self, fn, *args, **kwargs):
        """Encola una llamada en el hilo de Tk. Si la app se está cerrando
        (root destruido), lo ignora en silencio — antes, un cierre con la
        canción sonando soltaba excepciones del hilo del worker."""
        try:
            self.root.after(0, lambda: fn(*args, **kwargs))
        except (RuntimeError, tk.TclError, AttributeError):
            pass

    def _start_hotkey_listener(self):
        if not PYNPUT_OK:
            return

        def on_press(key):
            self._tecla_global(key)

        listener = pkb.Listener(on_press=on_press)
        listener.daemon = True
        listener.start()

    # ======================================================================
    # Modo práctica: la app escucha las teclas del usuario y espera a que
    # toque cada nota correcta antes de avanzar (la app no presiona nada)
    # ======================================================================
    def _start_practice_listener(self):
        if not PYNPUT_OK or self._practice_listener is not None:
            return

        def _letra(key):
            try:
                ch = key.char
            except AttributeError:
                ch = None
            if not ch:
                return None
            if ch.isalnum() or ch in VP_CHARS:
                return ch
            return None

        def on_press(key):
            ch = _letra(key)
            if ch:
                self._practice_keys.add(_canonica(ch))

        def on_release(key):
            ch = _letra(key)
            if ch:
                self._practice_keys.discard(_canonica(ch))

        self._practice_listener = pkb.Listener(on_press=on_press,
                                               on_release=on_release)
        self._practice_listener.daemon = True
        self._practice_listener.start()

    def _stop_practice_listener(self):
        if self._practice_listener is not None:
            try:
                self._practice_listener.stop()
            except Exception:
                pass
            self._practice_listener = None
        self._practice_keys.clear()

    def _wait_practice(self, notes):
        """En modo práctica: espera a que el usuario presione todas las
        teclas del grupo y luego a que las suelte (así una nota repetida
        obliga a tocarla de nuevo). Devuelve False si se detuvo."""
        requeridas = {_canonica(ch) for ch in notes}
        self._ui(self.lbl_estado.config,
                 text="🎹 Toca: " + " + ".join(sorted(requeridas)))
        while not self.stop_flag and not requeridas.issubset(self._practice_keys):
            time.sleep(0.03)
        if self.stop_flag:
            return False
        # exigir soltar antes de la siguiente nota (re-pisa las repetidas)
        while not self.stop_flag and (self._practice_keys & requeridas):
            time.sleep(0.03)
        return not self.stop_flag

    def _check_script_update(self):
        """Cada 5 s compara la fecha del archivo: si cambió en el disco,
        avisar que hay una versión nueva lista con ♻ Reiniciar."""
        if self._cerrando:
            return
        try:
            nuevo = os.path.getmtime(os.path.abspath(__file__))
        except OSError:
            nuevo = self._script_mtime
        if nuevo != self._script_mtime:
            self._script_mtime = nuevo
            try:
                if not self.playing:
                    self.lbl_estado.config(
                        text="♻ Hay una versión nueva de la app — pulsa ♻ Reiniciar")
            except tk.TclError:
                return
        try:
            self.root.after(5000, self._check_script_update)
        except (RuntimeError, tk.TclError):
            pass

    def _chequeo_internet_hilo(self):
        """Al iniciar (y desde el hilo de fondo): busca en internet si
        hay una versión más nueva y pregunta si querés actualizarla."""
        time.sleep(6)                    # que la app arranque tranquila
        if self._cerrando or not _act_urls()[0]:
            return
        remota = _version_remota()
        if self._cerrando or not _hay_actualizacion(remota, self.VERSION):
            return

        def preguntar(remota=remota):
            if self._cerrando:
                return
            if messagebox.askyesno(
                    "♻ Actualización disponible",
                    f"Salio AutoPiano {remota} (tenés {self.VERSION}).\n\n"
                    "¿Actualizar ahora? Se descarga sola y se reinicia\n"
                    "sin tocar tus partituras.",
                    parent=self.root):
                self._actualizar_internet_ui(remota)

        self._ui(preguntar)

    def _actualizar_internet_ui(self, remota):
        """Descarga la versión nueva con avance en el rótulo de estado
        y reinicia la app ya actualizada (los .json no se tocan)."""
        if getattr(self, "_actualizando", False):
            return              # ya hay una actualización en vuelo: no
                                # arrancar una segunda (dos .bat a la vez
                                # podrían pisarse al copiar el exe)
        if self.playing:
            self.stop_play()
        self._actualizando = True

        def avance(p):
            self._ui(self.lbl_estado.config,
                     text=f"⏳ Descargando versión {remota}… "
                          f"{int(p * 100)}%", fg="#ffe066")

        def worker():
            try:
                try:
                    res = _actualizar_internet(avance=avance)
                except Exception as e:
                    # la descarga falló o vino corrupta: la app SIGUE
                    # funcionando con la versión actual (no se tocó)
                    self._ui(self.lbl_estado.config,
                             text=f"✖ No se pudo actualizar: {e}",
                             fg="#ffd7d7")
                    return
                if res == "actualizado":
                    if getattr(sys, "frozen", False):
                        # el .bat espera a que cerremos, copia y reabre solo
                        self._ui(self.lbl_estado.config,
                                 text="♻ Actualizando… se reinicia solo",
                                 fg="#9fe870")
                        self._ui(self._on_close)
                    else:
                        # .py reescrito en el lugar: reabrir con lo nuevo
                        self._ui(self._restart_app)
                elif res == "al-dia":
                    self._ui(self.lbl_estado.config,
                             text="✔ Ya tenés la última versión",
                             fg="#9fe870")
                else:
                    self._ui(self.lbl_estado.config,
                             text="✖ No se pudo buscar la versión nueva",
                             fg="#ffd7d7")
            finally:
                self._actualizando = False

        threading.Thread(target=worker, daemon=True).start()

    def _restart_app(self):
        """Cierra (guardando todo) y vuelve a abrir la app con la versión
        actual del archivo — así los cambios nuevos se cargan al instante."""
        self._on_close()
        if getattr(sys, "frozen", False):
            # exe: se relanza a sí mismo (pasarle __file__ apuntaría a
            # una carpeta temporal _MEI que ya no va a existir)
            subprocess.Popen([sys.executable])
        else:
            subprocess.Popen([sys.executable, os.path.abspath(__file__)])

    def _on_close(self):
        if self._cerrando:
            return              # cierre doble (✕ + actualización a la vez):
                                # ya se cerró, no repetir (crasheaba con
                                # TclError al destruir dos veces)
        self._cerrando = True
        if self.playing:
            self.stop_play()
            time.sleep(0.2)
        # recordar la última sesión: partitura seleccionada y pizarrón
        try:
            if self._dirty and self._autosave_id:
                self.root.after_cancel(self._autosave_id)
                self._autosave_id = None
                self._autosave_board()
            # vaciar el guardado diferido de config por canción (si cerrás
            # la app justo después de cambiar velocidad no se pierde)
            if getattr(self, "_songsave_id", None):
                self.root.after_cancel(self._songsave_id)
                self._songsave_id = None
            self._guardar_song_settings()
            # ídem el guardado diferido de la config global
            if getattr(self, "_settings_save_id", None):
                self.root.after_cancel(self._settings_save_id)
                self._settings_save_id = None
            self._save_settings_quiet()
            self.settings["last_score"] = (getattr(self, "_score_actual", None)
                                           or self._current_score_name() or "")
            self.settings["last_board"] = self.board.get("1.0", "end-1c")[:20000]
            self._save_settings()
        except Exception:
            pass
        self._release_all_held()
        self._stop_practice_listener()
        self.root.destroy()


def main():
    root = tk.Tk()
    # 🗝 v4.24: sin clave vigente no se usa la app (se valida una sola
    # vez al activar; después sólo cheques de fecha local).
    ok, motivo, _ = _activacion_vigente()
    if not ok:
        root.withdraw()
        if not _dialogo_activacion(root, motivo):
            root.destroy()
            return
        root.deiconify()
    AutoPianoApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
