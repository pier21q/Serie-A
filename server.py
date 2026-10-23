"""Serie A Live - server locale.

Serve la pagina web (index.html) su http://127.0.0.1:8765. Il calcolo statistico sta in model.py.

Fonti dei dati (tutte rispondono senza blocchi):
  - ESPN, cioè i dati ufficiali delle partite: risultati live, calendario, classifica, formazioni ufficiali
    con le posizioni in campo, arbitro, statistiche di ogni partita (squadre e giocatori), rose, precedenti,
    stagione scorsa.
      * live ogni minuto durante le partite, altrimenti ogni 30 minuti
      * classifica ogni 5 minuti durante le partite, altrimenti ogni 2 ore
      * formazioni ufficiali ogni 10 minuti nell'ultima ora e mezza prima del calcio d'inizio
      * statistiche di ogni partita appena finisce
  - Understat: xG, xA, xG concessi, pressing (PPDA), passaggi chiave, minuti (ogni 6 ore e dopo le partite).
  - Fantacalcio.it: media voto e fantamedia; probabili formazioni e indisponibili nella settimana prima.
  - Wikipedia: allenatori, con le giornate in panchina.
Sofascore non si usa più: bloccava la rete dopo poche richieste.

Avvio:  python server.py            (apre la pagina nel browser)
        python server.py --no-open  (non apre il browser)
        python server.py --offline  (usa solo i dati salvati, nessuna richiesta esterna)
        python server.py --cloud    (su GitHub Actions, ogni 30 minuti: nessuna pagina web; riscarica tutte le
                                     fonti, ripubblica il sito nel ramo "sito" anche senza novità e salva i
                                     dati nel ramo "dati", poi esce)
"""
import asyncio
import collections
import difflib
import json
import math
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import time
import unicodedata
import zlib
import webbrowser
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urlencode, urlsplit

import aiohttp
from aiohttp import web

import europa
import fonti
import controlli
import letture
import model
import sito
import statistiche

ROOT = Path(__file__).resolve().parent
# leghe: una per processo, scelta con SERIEA_LEGA (di base la Serie A). Fuori dalla Serie A non c'è Fantacalcio.it:
# niente fanta, voti e designazioni anticipate; le probabili formazioni vengono da OneFootball. Ogni lega ha i suoi dati
# in una sottocartella e sul sito sta in una sottocartella (la Premier League in /premier/).
# Taratura (09/10/2026), con un controllo su 50 partite per lega che toglie ogni volta la partita dalle statistiche
# dei giocatori, confrontato con le quote reali dei ruoli su 430 partite (questa stagione e la scorsa). Si corregge
# solo dove le due misure vanno nella stessa direzione: gol dei difensori sovrastimati in entrambe le leghe, gialli
# degli attaccanti della Premier sottostimati. La vecchia correzione fissa degli attaccanti (model.F_CALIB) era nata
# da un controllo che includeva la partita stessa: tolta.
NO_F_CALIB = {"shots": 1.0, "sot": 1.0, "fouls": 1.0, "fouled": 1.0, "lamG": 1.0, "lamA": 1.0}
LEGHE = {
    "serie-a": {"name": "Serie A", "espn": "ita.1", "understat": "Serie_A", "wiki_en": "Serie A", "dir": "",
                "fantacalcio": True, "onefootball": None, "of_comp": "serie-a-13", "opta": "serie-a", "port": 8765,
                "calib": NO_F_CALIB, "roles": {"lamG": {"D": .90}}},
    "premier": {"name": "Premier League", "espn": "eng.1", "understat": "EPL", "wiki_en": "Premier League", "dir": "premier",
                "fantacalcio": False, "onefootball": "premier-league-9", "of_comp": "premier-league-9", "opta": "premier-league", "port": 8766,
                "calib": NO_F_CALIB, "roles": {"lamG": {"D": .80}, "lamY": {"F": 1.15}}},
    # dal 13/10/2026; correzioni per ruolo da fissare con taratura.py quando ci sono abbastanza partite con formazione ESPN
    "liga": {"name": "La Liga", "espn": "esp.1", "understat": "La_liga", "wiki_en": "La Liga", "dir": "liga",
             "fantacalcio": False, "onefootball": "laliga-10", "of_comp": "laliga-10", "opta": "la-liga", "port": 8767,
             "calib": NO_F_CALIB, "roles": {}},
    # dal 14/10/2026, allo stesso modo della Liga
    "bundesliga": {"name": "Bundesliga", "espn": "ger.1", "understat": "Bundesliga", "wiki_en": "Bundesliga", "dir": "bundesliga",
                   "fantacalcio": False, "onefootball": "bundesliga-1", "of_comp": "bundesliga-1", "opta": "bundesliga", "port": 8769,
                   "calib": NO_F_CALIB, "roles": {}},
    "ligue1": {"name": "Ligue 1", "espn": "fra.1", "understat": "Ligue_1", "wiki_en": "Ligue 1", "dir": "ligue1",
               "fantacalcio": False, "onefootball": "ligue-1-23", "of_comp": "ligue-1-23", "opta": "ligue-1", "port": 8770,
               "calib": NO_F_CALIB, "roles": {}},
    # dal 13/10/2026. Coppa: squadre di campionati diversi, quindi la forza viene da europa.py (campionati e coppe
    # europee insieme), non dalle partite della Champions; niente Understat né Wikipedia della competizione
    # dal 14/10/2026. Understat e Opta Analyst non li coprono: gli xG di squadre e giocatori vengono dalla posizione dei
    # tiri nella cronaca ESPN (statistiche.understat_from_espn, ESPN_XG); niente statistiche Opta dei giocatori
    "eredivisie": {"name": "Eredivisie", "espn": "ned.1", "understat": None, "wiki_en": "Eredivisie", "dir": "eredivisie",
                   "fantacalcio": False, "onefootball": "eredivisie-36", "of_comp": "eredivisie-36", "opta": None, "port": 8771,
                   "calib": NO_F_CALIB, "roles": {}, "minor": True},
    "portugal": {"name": "Liga Portugal", "espn": "por.1", "understat": None, "wiki_en": "Primeira Liga", "dir": "portugal",
                 "fantacalcio": False, "onefootball": "liga-portugal-35", "of_comp": "liga-portugal-35", "opta": None, "port": 8772,
                 "calib": NO_F_CALIB, "roles": {}, "minor": True},
    "superlig": {"name": "Süper Lig", "espn": "tur.1", "understat": None, "wiki_en": "Süper Lig", "dir": "superlig",
                 "fantacalcio": False, "onefootball": "sueper-lig-8", "of_comp": "sueper-lig-8", "opta": None, "port": 8773,
                 "calib": NO_F_CALIB, "roles": {}, "minor": True},
    "champions": {"name": "Champions League", "espn": "uefa.champions", "understat": None, "wiki_en": None, "dir": "champions",
                  "fantacalcio": False, "onefootball": "uefa-champions-league-5", "of_comp": "uefa-champions-league-5",
                  "opta": "uefa-champions-league", "port": 8768, "calib": NO_F_CALIB, "roles": {}, "cup": True},
}
# zone della classifica per posizione: solo i posti sicuri per la stagione dopo (Champions, Europa, Conference), più
# la retrocessione. Le note di ESPN non vanno bene: segnavano la vincitrice della coppa della stagione scorsa (Athletic
# decimo in Europa League) e il quinto posto Champions solo per alcune leghe. La coppa nazionale (Europa League; in
# Inghilterra la coppa di Lega va in Conference) e il quinto posto Champions alle due nazioni con i migliori risultati
# europei della stagione si sanno in primavera e possono far scalare le posizioni: lo spiega la nota sotto la classifica.
ZONE_RULES = {"serie-a": [(1, 4, "Champions League"), (5, 5, "Europa League"), (6, 6, "Conference League")],
              "premier": [(1, 4, "Champions League"), (5, 5, "Europa League")],
              "liga": [(1, 4, "Champions League"), (5, 5, "Europa League"), (6, 6, "Conference League")],
              "bundesliga": [(1, 4, "Champions League"), (5, 5, "Europa League"), (6, 6, "Conference League")],
              # Francia quinta nel ranking UEFA: tre posti diretti in Champions, il quarto ai preliminari
              "ligue1": [(1, 3, "Champions League"), (4, 4, "Champions League Qualification"), (5, 5, "Europa League"),
                         (6, 6, "Conference League")],
              # Olanda sesta nel ranking UEFA, Portogallo e Turchia più giù: le posizioni come le note di ESPN
              "eredivisie": [(1, 2, "Champions League"), (3, 3, "Champions League Qualification"),
                             (4, 4, "Europa League Qualification"), (5, 5, "Conference League Qualification")],
              "portugal": [(1, 1, "Champions League"), (2, 2, "Champions League Qualification"),
                           (3, 3, "Europa League Qualification"), (4, 4, "Conference League Qualification")],
              "superlig": [(1, 1, "Champions League"), (2, 2, "Champions League Qualification"),
                           (3, 3, "Europa League Qualification"), (4, 4, "Conference League Qualification")],
              # Champions: le prime 8 agli ottavi, dalla 9ª alla 24ª agli spareggi, le altre fuori
              "champions": [(1, 8, "Round of 16"), (9, 24, "Playoffs"), (25, 36, "Eliminated")]}
LEGA_KEY = os.environ.get("SERIEA_LEGA") or "serie-a"
LEGA = LEGHE[LEGA_KEY]
model.LEAGUE = LEGA["name"]
model.F_CALIB = dict(model.F_CALIB, **(LEGA.get("calib") or {}))
model.ROLE_CALIB = LEGA.get("roles") or {}
CUP = bool(LEGA.get("cup"))
ESPN_XG = not LEGA["understat"] and not CUP   # campionato senza Understat: i suoi dati nello stesso formato, fatti con ESPN
# anche in coppa gli xG di squadre e giocatori vengono dai tiri della cronaca ESPN (stagione in corso: la base dei
# giocatori restano i loro campionati, vedi cup_prior_players)
SHOT_XG = ESPN_XG or CUP
if LEGA["understat"]:
    statistiche.UNDERSTAT = statistiche.UNDERSTAT.replace("Serie_A", LEGA["understat"])
    statistiche.UNDERSTAT_REF = statistiche.UNDERSTAT_REF.replace("Serie_A", LEGA["understat"])
if LEGA["wiki_en"]:
    fonti.WIKI_EN_TITLE = "{a}–{b:02d} " + LEGA["wiki_en"]
# dati salvati e immagini stanno fuori dalla cartella dell'app, che puo' essere sincronizzata con iCloud
DATA_BASE = Path(os.environ.get("SERIEA_DATA_DIR") or Path.home() / "Library" / "Application Support" / "Serie A Live")
DATA_DIR = DATA_BASE / LEGA["dir"] if LEGA["dir"] else DATA_BASE
CACHE = DATA_DIR / "cache"
IMGDIR = CACHE / "img"
IMGDIR.mkdir(parents=True, exist_ok=True)
DATA_FILE = CACHE / "data.json"
SQUAD_FILE = CACHE / "squads.json"
PRIOR_FILE = CACHE / "prior.json"
MATCH_FILE = CACHE / "matches.json"
COACH_FILE = CACHE / "coaches.json"
ESPN_FILE = CACHE / "espn.json"
EXTRA_FILE = CACHE / "fonti.json"   # fonti di riserva: fantacalcio.it, Wikipedia
REG_FILE = CACHE / "giocatori.json"   # anagrafica: stesso giocatore su ESPN, Understat e Fantacalcio.it
FC_STATS_FILE = CACHE / "fantacalcio-statistiche.json"
OPTA_FILE = CACHE / "opta.json"   # statistiche Opta della stagione (da Opta Analyst)
HISTORY_FILE = DATA_DIR / "history.json"   # storico dei pronostici: non sta in cache perche' non si puo' ricreare
FANTA_FILE = DATA_DIR / "fanta.json"       # rose del fantacalcio
SNAPSHOT_FILE = DATA_DIR / "fotografia.json"   # dati compatti per la versione tascabile (artefatto)
SITE_ROOT = Path(os.environ.get("SERIEA_SITE_DIR") or DATA_BASE / "sito")   # sito su GitHub Pages (repository git locale)
SITE_DIR = SITE_ROOT / LEGA["dir"] if LEGA["dir"] else SITE_ROOT          # pagina di questa lega dentro il sito
SITE_CONF = DATA_DIR / "sito.json"            # {"remote": "https://github.com/<utente>/<repository>.git"}
CLOUD_FILE = DATA_DIR / "esecuzione.json"     # su GitHub Actions: com'è andato l'ultimo aggiornamento

PORT = int(os.environ.get("SERIEA_PORT") or LEGA["port"])
ESPN_SITE = os.environ.get("SERIEA_ESPN", f"https://site.api.espn.com/apis/site/v2/sports/soccer/{LEGA['espn']}")
ESPN_STAND = os.environ.get("SERIEA_ESPN_STAND", f"https://site.api.espn.com/apis/v2/sports/soccer/{LEGA['espn']}/standings")
UA = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36"
WIKI_UA = "SerieALive/1.0 (https://github.com/pier21q/Serie-A)"   # come chiede Wikipedia ai programmi
DATA_VERSION = 4   # 4: statistiche da ESPN, Understat e Fantacalcio.it (non più Sofascore)

# ogni fonte si riscarica a ogni aggiornamento, cioè ogni 30 minuti (25, per non saltarne uno per pochi secondi)
NEWS_EVERY = 25 * 60
# ESPN
LIVE_EVERY, IDLE_EVERY = 60, 1800
STAND_LIVE, STAND_IDLE = 300, NEWS_EVERY
MONTHS_EVERY = NEWS_EVERY
FC_NEAR, FC_FAR = NEWS_EVERY, NEWS_EVERY   # probabili formazioni e indisponibili, nella settimana prima
WIKI_EVERY = NEWS_EVERY            # allenatori da Wikipedia, per vedere presto esoneri e dimissioni
PRE_EVERY = NEWS_EVERY             # precedenti e arbitro designato (ESPN), nei 3 giorni prima
US_EVERY = NEWS_EVERY              # Understat e Fantacalcio.it
OPTA_EVERY = 6 * 3600             # Opta: Opta Analyst aggiorna i dati una volta al giorno
ROSTER_EVERY = 7 * 86400           # rose da ESPN: una volta a settimana (cambiano solo col mercato)
CLOUD = "--cloud" in sys.argv
SITE_EVERY = 15 * 60               # sito dal Mac: al massimo ogni 15 minuti (su GitHub a ogni aggiornamento)
LINEUP_EVERY = 600
MATCH_LENGTH = 150 * 60        # durata massima stimata di una partita dal calcio d'inizio

BASE_FIELDS = [
    "goals", "assists", "rating", "expectedGoals", "expectedAssists", "minutesPlayed",
    "appearances", "totalShots", "shotsOnTarget", "keyPasses", "bigChancesCreated",
    "bigChancesMissed", "successfulDribbles", "tackles", "interceptions", "clearances",
    "saves", "cleanSheet", "yellowCards", "redCards", "accuratePassesPercentage",
    "goalsConceded", "aerialDuelsWon", "totalDuelsWon", "accurateLongBalls",
    "penaltyGoals", "goalsPrevented",
]
EXTRA_FIELDS = [
    "fouls", "wasFouled", "matchesStarted", "yellowRedCards", "directRedCards", "dispossessed",
    "dribbledPast", "touches", "totalContest", "penaltyWon", "penaltyConceded", "possessionWonAttThird",
    "ballRecovery", "groundDuelsWon", "aerialLost", "duelLost", "totalCross", "accurateCrosses",
    "offsides", "blockedShots", "penaltiesTaken", "totalPasses",
]

FETCH_JS = """async u => { try { const r = await fetch(u);
    return {s: r.status, t: await r.text()} } catch (e) { return {s: 0, t: String(e)} } }"""

STATE = {"data": None}
STATUS = {"mode": "avvio", "espnAt": None, "espnError": None, "statsAt": None, "usAt": None, "fcStatsAt": None,
          "nextCheck": None}
IMG_MISSING = set()
HTTP = {"espn": None, "web": None}   # ESPN vuole l'identificazione standard di aiohttp; "web" per gli altri siti


def errtxt(e):
    """Testo di un errore: alcune eccezioni (es. una richiesta scaduta) non hanno messaggio, allora il loro tipo."""
    return str(e) or type(e).__name__


def log(msg):
    # sul Mac le leghe scrivono nella stessa finestra: le altre si riconoscono dal nome
    print(f"[{time.strftime('%d/%m %H:%M:%S')}] " + (f"[{LEGA['name']}] " if LEGA["dir"] else "") + str(msg), flush=True)


def load_json(path, default):
    try:
        return json.loads(path.read_text())
    except Exception:
        return default


def save_json(path, obj):
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(obj, ensure_ascii=False))
    tmp.replace(path)


PRIOR = load_json(PRIOR_FILE, {})
MATCHES = load_json(MATCH_FILE, {})
HISTORY = load_json(HISTORY_FILE, {"matches": {}})
SQUADS = load_json(SQUAD_FILE, {})
FANTA = load_json(FANTA_FILE, {"teams": []})
COACHES = load_json(COACH_FILE, {})
ESPNMAP = load_json(ESPN_FILE, {"teams": {}, "events": {}, "priorTeams": {}})
EXTRA = load_json(EXTRA_FILE, {})
REG = load_json(REG_FILE, {"info": {}, "espn": {}, "us": {}, "fc": {}})
REG.setdefault("opta", {})
VERSION = {"matches": 0, "squads": 0, "coaches": 0, "forza": 0}
# versione del codice: cambia a ogni modifica di server.py o model.py
CODE_VERSION = str(int(max((ROOT / f).stat().st_mtime for f in ("server.py", "model.py", "fonti.py", "statistiche.py", "sito.py"))))


def match_entry(e):
    x = MATCHES.setdefault(str(e["id"]), {})
    x.update(homeId=e["home"]["id"], awayId=e["away"]["id"], start=e["start"], round=e.get("round"))
    return x



# ---------- ESPN ----------

# nomi da ricondurre a quelli di ESPN: squadre e giocatori che le fonti scrivono in modo diverso (Understat inverte nome
# e cognome di Fatawu Issahaku)
ALIASES = {"internazionale": "inter", "inter milan": "inter", "hellas verona": "verona", "abdul fatawu": "fatawu issahaku",
           # Bundesliga: i nomi tedeschi di Wikipedia e quelli inglesi di ESPN
           "koln": "cologne", "hamburger": "hamburg",
           # Süper Lig: Wikipedia «Amedspor» ed «Erzurumspor», ESPN «Amed SFK» ed «Erzurum BB»
           "amedspor": "amed", "erzurumspor": "erzurum"}
STOP = {"fc", "ac", "as", "ss", "us", "calcio", "sc", "cfc", "bc", "afc", "club", "ssc", "acf", "1913", "1907"}
ESPN_STATUS_IT = {"STATUS_FIRST_HALF": ("inprogress", "1° tempo", 6), "STATUS_HALFTIME": ("inprogress", "Intervallo", 31),
                  "STATUS_SECOND_HALF": ("inprogress", "2° tempo", 7), "STATUS_FULL_TIME": ("finished", "Finale", 100),
                  "STATUS_FINAL": ("finished", "Finale", 100), "STATUS_SCHEDULED": ("notstarted", "Da giocare", 0),
                  "STATUS_POSTPONED": ("postponed", "Rinviata", 60), "STATUS_CANCELED": ("postponed", "Annullata", 70),
                  "STATUS_ABANDONED": ("postponed", "Sospesa", 70)}
DEPTH = {"G": 0, "CD": 1, "CD-L": 1, "CD-R": 1, "RB": 1, "LB": 1, "RWB": 1.5, "LWB": 1.5, "DM": 1.6, "CDM": 1.6,
         "RM": 2, "LM": 2, "CM": 2, "CM-L": 2, "CM-R": 2, "AM": 3, "AM-L": 3, "AM-R": 3, "RW": 3.5, "LW": 3.5,
         "SS": 3.8, "CF-L": 3.8, "CF-R": 3.8, "CF": 4, "F": 4, "RF": 4, "LF": 4}


def tok_seq(n):
    """Parole di un nome, normalizzate e in ordine (senza «jr», «junior»)."""
    s = unicodedata.normalize("NFD", (n or "").translate(model.TRANSLIT)).encode("ascii", "ignore").decode().lower()
    s = re.sub(r"[^a-z ]+", " ", s)
    for a, b in ALIASES.items():
        s = s.replace(a, b)
    out = [w for w in s.split() if w not in STOP]
    # in fondo: «jr», «junior» e le iniziali di Fantacalcio.it («Martinez L.»)
    while len(out) > 1 and (out[-1] in ("jr", "junior", "ii", "iii") or len(out[-1]) == 1):
        out.pop()
    return out


def tokens(*names):
    out = set()
    for n in names:
        out |= set(tok_seq(n))
    return out


def same_person(a, b):
    """Possono essere la stessa persona: una parte del cognome in comune («Matìas Soulè Malvano» e «Matías Soulé»),
    anche scritto attaccato («Del Prato» e «Delprato») o con una piccola differenza («Halal» e «Halhal»). Il nome di
    battesimo da solo non basta: «Lewis Hall» non è «Lewis Miley». Un nome di una parola sola («Gabriel», «Rodri», come
    li scrive Understat) può essere una parola qualsiasi dell'altro."""
    x, y = tok_seq(a), tok_seq(b)
    if not x or not y:
        return False
    if len(x) == 1 or len(y) == 1:
        return bool(set(x) & set(y))
    sx, sy = x[1:], y[1:]
    return (bool(set(sx) & set(sy)) or "".join(sx) == "".join(sy)
            or difflib.SequenceMatcher(None, x[-1], y[-1]).ratio() >= .85)


def map_team(et, teams, store="teams"):
    """Squadra ESPN -> id della squadra nell'app (per nome, con qualche alias)."""
    eid = str(et.get("id"))
    known = ESPNMAP.setdefault(store, {}).get(eid)
    if known and str(known) in teams:
        return str(known)
    tk = tokens(et.get("displayName"), et.get("shortDisplayName"), et.get("name"), et.get("location"))
    best, bs = None, 0
    for sid, t in teams.items():
        sc = len(tk & tokens(t.get("fullName"), t.get("name")))
        if sc and (t.get("code") or "").upper() == (et.get("abbreviation") or "").upper():
            sc += .5
        if sc > bs:
            best, bs = sid, sc
    if best:
        ESPNMAP[store][eid] = best
    return best


def espn_time(s):
    return int(datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone(timezone.utc).timestamp())


def espn_event(e, teams):
    """Partita ESPN nel formato della pagina."""
    c = (e.get("competitions") or [{}])[0]
    comp = {x.get("homeAway"): x for x in c.get("competitors") or []}
    if "home" not in comp or "away" not in comp:
        return None
    h, a = map_team(comp["home"]["team"], teams), map_team(comp["away"]["team"], teams)
    if not h or not a:
        return None
    st = e.get("status") or c.get("status") or {}
    typ = st.get("type") or {}
    state, text, code = ESPN_STATUS_IT.get(typ.get("name"), (
        {"pre": "notstarted", "in": "inprogress", "post": "finished"}.get(typ.get("state"), "notstarted"),
        typ.get("description") or "", None))
    score = lambda x: int(x["score"]) if state in ("inprogress", "finished") and str(x.get("score", "")).isdigit() else None
    out = {"espn": str(e["id"]), "start": espn_time(e.get("date") or c.get("date")), "status": state, "statusText": text,
           "code": code, "clock": st.get("displayClock") if state == "inprogress" and code != 31 else None,
           "home": teams[h], "away": teams[a], "hs": score(comp["home"]), "as": score(comp["away"])}
    if CUP:   # fase (league-phase, knockout-round-playoffs, round-of-16, ...) e andata o ritorno
        note = ((c.get("notes") or [{}])[0] or {}).get("headline") or ""
        out["stage"] = (e.get("season") or {}).get("slug")
        out["leg"] = 2 if note.startswith("2nd Leg") else 1 if note.startswith("1st Leg") else None
        out["neutral"] = bool(c.get("neutralSite")) or out["stage"] == "final"
        adv = [x["homeAway"] for x in (comp["home"], comp["away"]) if x.get("advance") or (out["stage"] == "final" and x.get("winner"))]
        if state == "finished" and len(adv) == 1:
            out["adv"] = adv[0]   # chi passa il turno (anche ai rigori) o vince la finale
    return out


def cur_teams(d):
    return {sid: o["team"] for sid, o in (d.get("teams") or {}).items()}


async def espn_get(url, **params):
    async with HTTP["espn"].get(url, params=params or None, timeout=aiohttp.ClientTimeout(total=25)) as r:
        if r.status != 200:
            raise RuntimeError(f"ESPN HTTP {r.status}")
        return await r.json(content_type=None)


def merge_events(d, evs):
    """Aggiorna calendario, risultati e live con le partite di ESPN."""
    known = {}
    for lst in ("next", "played", "live"):
        for e in d.get(lst) or []:
            known.setdefault((e["home"]["id"], e["away"]["id"]), []).append(e)
    ended = []
    by_id = {}
    for lst in ("next", "played", "live"):
        for e in d.get(lst) or []:
            by_id[str(e["id"])] = e
    rounds = sorted([(e["start"], e["round"]) for e in by_id.values() if e.get("round")])
    for x in evs:
        mapped = ESPNMAP.setdefault("events", {}).get(x["espn"])
        base = by_id.get(str(mapped)) if mapped is not None else None
        if base is None:
            cand = [e for e in known.get((x["home"]["id"], x["away"]["id"]), []) if abs(e["start"] - x["start"]) < 10 * 86400]
            base = cand[0] if cand else None
        eid = base["id"] if base else (mapped or f"e{x['espn']}")
        ESPNMAP["events"][x["espn"]] = eid
        ev = dict(base or {})
        was = ev.get("status")
        ev.update({k: v for k, v in x.items() if k not in ("home", "away")}, id=eid)
        ev["home"], ev["away"] = (base or x)["home"], (base or x)["away"]
        if not ev.get("round") and rounds and not LEGA["dir"]:   # le altre leghe: number_rounds
            near = min(rounds, key=lambda r: abs(r[0] - ev["start"]))
            ev["round"] = near[1] if abs(near[0] - ev["start"]) < 3 * 86400 else None
        if was in ("notstarted", "inprogress", None) and ev["status"] == "finished" and base is not None:
            ended.append(ev)
        by_id[str(eid)] = ev
    now = time.time()
    allev = list(by_id.values())
    d["live"] = sorted([e for e in allev if e["status"] == "inprogress"], key=lambda e: e["start"])
    # tutta la stagione (380 partite al massimo): le statistiche di squadre e giocatori si sommano da qui
    d["played"] = sorted([e for e in allev if e["status"] == "finished"], key=lambda e: -e["start"])[:420]
    d["next"] = sorted([e for e in allev if e["status"] in ("notstarted", "postponed") and e["start"] > now - 3 * 86400],
                       key=lambda e: e["start"])
    venue_standings(d)
    return ended


def venue_standings(d):
    """Classifiche in casa e in trasferta dai risultati (ESPN dà solo quella generale): a parità di punti contano
    differenza reti e gol fatti."""
    vt = model.venue_tables(d.get("played"))
    for k in ("home", "away"):
        rows = sorted(vt[k], key=lambda r: (-r["pts"], -(r["gf"] - r["ga"]), -r["gf"], r["team"].get("name") or ""))
        for i, r in enumerate(rows):
            r["pos"] = i + 1
        if rows:
            d.setdefault("standings", {})[k] = rows


async def espn_schedule(d, months):
    """Calendario e risultati dei mesi indicati (formato AAAAMM) oppure di un giorno (AAAAMMGG)."""
    teams = cur_teams(d)
    evs = []
    for m in months:
        j = await espn_get(ESPN_SITE + "/scoreboard", dates=m)
        evs += [x for x in (espn_event(e, teams) for e in j.get("events", [])) if x]
    ended = merge_events(d, evs)
    if CUP:
        cup_rounds(d)
    else:   # anche la Serie A: le partite oltre il calendario di Fantacalcio.it (che arriva poche giornate avanti) non
        number_rounds(d)   # avevano la giornata; quelle che ce l'hanno la tengono
    d["updatedAt"] = time.time()
    return ended


ZONE_CANON = (("champions", "Champions League"), ("europa", "Europa League"), ("conference", "Conference League"),
              ("relegat", "Relegation"))


# in fondo alla classifica: (retrocesse direttamente, allo spareggio). In Germania e in Francia la terzultima gioca lo
# spareggio con la terza della serie B
RELEGATION = {"bundesliga": (2, 1), "ligue1": (2, 1), "eredivisie": (2, 1), "portugal": (2, 1)}   # in Turchia ne scendono tre


def zone_at(pos, n=20):
    """Zona della classifica di una posizione, con le regole della lega (ZONE_RULES): nei campionati le ultime tre
    retrocedono (in Germania e in Francia due, e la terzultima va allo spareggio), in coppa no."""
    down, playoff = RELEGATION.get(LEGA_KEY, (3, 0))
    if not CUP and pos and pos > n - down:
        return "Relegation"
    if not CUP and pos and pos > n - down - playoff:
        return "Relegation Playoff"
    return next((z for a, b, z in ZONE_RULES.get(LEGA_KEY, []) if a <= (pos or 0) <= b), None)


def canon_zone(desc):
    """Zona della classifica con un nome unico: ESPN la scrive in modi diversi (Relegated, Relegation,
    Conference League qualifying...), le pagine riconoscono questi quattro."""
    d = (desc or "").lower()
    return next((v for k, v in ZONE_CANON if k in d), None)


async def espn_standings(d):
    teams = cur_teams(d)
    j = await espn_get(ESPN_STAND)
    ch = j.get("children") or []
    entries = ((ch[0].get("standings") if ch else j.get("standings")) or {}).get("entries") or []
    # le zone (Champions, Europa, Conference, retrocessione) vanno con la posizione: zone_at, non le note di ESPN
    rows = []
    for e in entries:
        sid = map_team(e.get("team") or {}, teams)
        if not sid:
            continue
        S = {s.get("name"): s.get("value") for s in e.get("stats") or []}
        num = lambda k: int(S.get(k) or 0)
        rows.append({"team": teams[sid], "pos": num("rank"), "p": num("gamesPlayed"), "w": num("wins"), "d": num("ties"),
                     "l": num("losses"), "gf": num("pointsFor"), "ga": num("pointsAgainst"), "pts": num("points"),
                     "zone": zone_at(num("rank"), len(entries))})
    if len(rows) >= 18:
        d["standings"]["total"] = sorted(rows, key=lambda r: r["pos"])
        d["updatedAt"] = time.time()


def pos_from_code(c):
    c = (c or "").upper()
    if c == "G":
        return "G"
    if c.startswith("CD") or c in ("RB", "LB", "RWB", "LWB", "D"):
        return "D"
    if c in ("F", "CF", "RF", "LF", "RW", "LW", "SS") or c.startswith("CF"):
        return "F"
    return "M"


def lateral(c):
    c = (c or "").upper()
    if c.endswith("-R"):
        return .5
    if c.endswith("-L"):
        return -.5
    if c[:1] == "R":
        return 1.0
    if c[:1] == "L":
        return -1.0
    return 0.0


def reg_score(name, x, jersey=None):
    tk, pt = tokens(name), tokens(x.get("name"))
    if not tk or not pt or not same_person(name, x.get("name")):   # prima bastava il nome di battesimo
        return 0.0
    sa, sb = tok_seq(name), tok_seq(x.get("name"))
    # cognome uguale, anche scritto attaccato («Dasilva» e «Da Silva») o con una piccola differenza («Halal»)
    sur = (sa[-1] in pt or "".join(sa[1:]) == "".join(sb[1:])
           or difflib.SequenceMatcher(None, sa[-1], sb[-1]).ratio() >= .85)
    sc = 3.0 * len(tk & pt) + (2.0 if sur else 0)
    if jersey and str(x.get("num") or "") == str(jersey):
        sc += 2.5
    return sc


def reg_find(name, team_ids, jersey=None, need=4.0, espn=None, skip=()):
    """Giocatore dell'anagrafica con questo nome (nelle squadre indicate, o in tutte se None). Con espn (id ESPN di chi
    si cerca) salta chi ha già un altro id ESPN: per ESPN due id diversi sono sempre due persone diverse. skip: giocatori
    già collegati a un'altra persona della stessa fonte."""
    teams = {str(t) for t in team_ids if t} if team_ids else None
    best, bs = None, 0.0
    for cid, x in REG["info"].items():
        if teams is not None and str(x.get("teamId")) not in teams:
            continue
        if cid in skip:
            continue
        if espn and x.get("espnId") and str(x["espnId"]) != str(espn):
            continue
        sc = reg_score(name, x, jersey)
        if sc > bs:
            best, bs = cid, sc
    return best if bs >= need else None


def canon_espn(eid, name, team_id, jersey=None, code=None, move=True):
    """Id del giocatore ESPN nell'anagrafica (lo stesso usato da formazioni e statistiche); se è nuovo lo aggiunge."""
    eid = str(eid)
    cid = REG["espn"].get(eid)
    if cid is None:
        cid = reg_find(name, [team_id], jersey, espn=eid) if team_id else None
        if cid is None:
            cid = reg_find(name, None, None, need=8.0, espn=eid)   # arrivato da un'altra squadra
        if cid is None:
            cid = str(-int(eid))
            REG["info"][cid] = {"name": name, "teamId": str(team_id) if team_id and move else None, "num": jersey,
                                "pos": pos_from_code(code) if code and code != "SUB" else None}
        REG["espn"][eid] = cid
    x = REG["info"].setdefault(cid, {"name": name})
    x["espnId"] = eid
    if move and team_id:
        x["teamId"] = str(team_id)
    if jersey and move:
        x["num"] = jersey
    if not x.get("pos") and code and code != "SUB":
        x["pos"] = pos_from_code(code)
    return cid


def map_athlete(team_id, a):
    """Giocatore ESPN -> id dell'anagrafica (per nome e numero di maglia)."""
    ath = a.get("athlete") or {}
    name = ath.get("displayName") or ath.get("fullName") or ""
    cid = canon_espn(ath.get("id") or 0, name, team_id, a.get("jersey"), ((a.get("position") or {}).get("abbreviation") or "").upper())
    return int(cid), (REG["info"].get(cid) or {}).get("name") or name


def espn_side(r, team_id, ident=None):
    roster = r.get("roster") or []
    code = lambda a: ((a.get("position") or {}).get("abbreviation") or "").upper()
    starters = [a for a in roster if a.get("starter")]
    subs = [a for a in roster if not a.get("starter")]
    gk = [a for a in starters if code(a) == "G"]
    out = sorted([a for a in starters if code(a) != "G"], key=lambda a: DEPTH.get(code(a), 2))
    lines = model.parse_formation(r.get("formation")) or []
    ordered, idx = gk[:1], 0
    for k in lines:
        grp = sorted(out[idx:idx + k], key=lambda a: -lateral(code(a)))   # da destra a sinistra
        ordered += grp
        idx += k
    ordered += out[idx:] + gk[1:]

    def conv(a):
        pid, nm = ident(a) if ident else map_athlete(team_id, a)
        return {"id": pid, "name": nm, "pos": pos_from_code(code(a)), "num": a.get("jersey"), "espnPos": code(a)}
    return {"formation": r.get("formation"), "starters": [conv(a) for a in ordered], "subs": [conv(a) for a in subs],
            "missing": [], "ordered": True}


def match_roles(j):
    """Da un riepilogo ESPN di una partita finita: per ogni squadra i ruoli in campo (dal modulo) e il ruolo
    di chi ha segnato e di chi ha fatto l'assist. Chi entra dalla panchina prende il ruolo di chi esce."""
    ros = {r.get("homeAway"): r for r in j.get("rosters") or []}
    if not (ros.get("home", {}).get("roster") and ros.get("away", {}).get("roster")):
        return None
    ident = lambda a: (str((a.get("athlete") or {}).get("id")), (a.get("athlete") or {}).get("displayName"))
    role, team_side, out = {}, {}, {}
    for side in ("home", "away"):
        r = ros[side]
        team_side[str((r.get("team") or {}).get("id"))] = side
        xi = espn_side(r, None, ident)
        lay = model.xi_layout(xi)
        slots = {}
        for pid, c in lay.items():
            fam = model.ROLE_FAMILY.get(c["role"])
            role[pid] = fam
            if fam:
                slots[fam] = slots.get(fam, 0) + 1
        out[side] = {"form": xi.get("formation"), "slots": slots, "g": [], "a": [], "og": 0}
    for team, pin, pout in fonti.espn_subs(j):
        if pout in role and pin not in role:
            role[pin] = role[pout]
    for g in fonti.espn_goals(j):
        side = team_side.get(g["team"])
        if not side:
            continue
        if g["og"]:
            out[side]["og"] += 1
            continue
        out[side]["g"].append(role.get(g["g"]) or "?")
        if g["a"]:
            out[side]["a"].append(role.get(g["a"]) or "?")
    return out


def keep_odds(x, e, j):
    """Quote 1X2 del mercato (fonti.espn_odds): prima del fischio d'inizio si aggiornano fino all'ultima (la chiusura);
    dopo restano quelle. Per una partita già giocata senza quote salvate valgono quelle di chiusura del riepilogo. La
    chiave c'è sempre dopo il primo tentativo (anche None, se ESPN non le ha) così non si riscarica all'infinito."""
    now = time.time()
    od = fonti.espn_odds(j)
    if now < e["start"]:
        if od:
            x["odds"] = dict(od, at=round(now))
        else:
            x.setdefault("odds", None)
    elif e.get("status") == "finished" and not x.get("odds"):
        x["odds"] = dict(od, at=round(now), close=True) if od else None


async def espn_summary(e):
    """Formazioni ufficiali e arbitro di una partita, da ESPN."""
    j = await espn_get(ESPN_SITE + "/summary", event=e["espn"])
    x = match_entry(e)
    x["espnAt"] = time.time()
    keep_odds(x, e, j)
    ros = {r.get("homeAway"): r for r in j.get("rosters") or []}
    if ros.get("home", {}).get("roster") and ros.get("away", {}).get("roster"):
        miss = {s: ((x.get("lineups") or {}).get(s) or {}).get("missing") or [] for s in ("home", "away")}
        caut = {s: ((x.get("lineups") or {}).get(s) or {}).get("cautioned") or [] for s in ("home", "away")}
        lu = {"confirmed": True, "source": "espn",
              "home": espn_side(ros["home"], e["home"]["id"]), "away": espn_side(ros["away"], e["away"]["id"])}
        for s in ("home", "away"):
            lu[s]["missing"] = miss[s]
            lu[s]["cautioned"] = caut[s]   # i diffidati restano quelli di Fantacalcio.it
        x["lineups"] = lu
        if e.get("status") == "finished":
            x["final"] = True
    if e.get("status") == "finished":
        x["cards"] = fonti.espn_cards(j) or {}
        x["roles"] = match_roles(j) or {}
        x["box"] = statistiche.box_from_summary(j) or {}
        x["ev"] = letture.parse_espn(j)   # cronaca (Opta): come sono nati gol e occasioni, per le letture
    for o in (j.get("gameInfo") or {}).get("officials") or []:
        if ((o.get("position") or {}).get("name") or "").lower() == "referee" and o.get("fullName"):
            ref = x.get("referee") or {}
            if tokens(ref.get("name")) != tokens(o["fullName"]):
                x["referee"] = {"name": o["fullName"]}
    return bool((x.get("lineups") or {}).get("confirmed"))


def summaries_due(d, now):
    """Partite di cui scaricare da ESPN le formazioni: imminenti, in corso, e giocate senza formazione salvata."""
    due = []
    for e in (d.get("live") or []) + (d.get("next") or []):
        if not e.get("espn"):
            continue
        x = MATCHES.get(str(e["id"])) or {}
        lu = x.get("lineups") or {}
        h = (e["start"] - now) / 3600
        if (lu.get("source") != "espn" and (e["status"] == "inprogress" or 0 <= h <= 1.5)
                and now - x.get("espnAt", 0) >= LINEUP_EVERY):
            due.append((0, e))
    for e in d.get("played") or []:
        x = MATCHES.get(str(e["id"])) or {}
        missing = ("cards" not in x or "roles" not in x or "box" not in x
                   or (x.get("ev") or {}).get("v") != letture.EV_VERSION)   # cronaca letta con una versione vecchia
        # l'arbitro a volte ESPN lo aggiunge giorni dopo (in Premier): si riprova ogni 6 ore per tre giorni
        noref = not (x.get("referee") or {}).get("name") and now - e["start"] < 3 * 86400
        wait = 120 if missing else 3600 if not x.get("final") else 6 * 3600
        if e.get("espn") and (not x.get("final") or missing or noref) and now - x.get("espnAt", 0) >= wait:
            due.append((1, e))
        elif e.get("espn") and "odds" not in x and now - x.get("espnAt", 0) >= 120:   # quote di chiusura
            due.append((2, e))
    return [e for _, e in sorted(due, key=lambda t: t[0])]


# Champions: dopo le 8 giornate della fase campionato, i turni a eliminazione diretta (andata e ritorno; finale secca)
KO_STAGES = ["knockout-round-playoffs", "round-of-16", "quarterfinals", "semifinals", "final"]
KO_NAMES = ["Spareggi", "Ottavi", "Quarti", "Semifinali", "Finale"]


def round_label(r):
    """Nome di un turno: «3ª giornata» o, in coppa, «Ottavi – andata»."""
    if r is None:
        return None
    if CUP and r > 8:
        i, leg = divmod(r - 9, 2)
        if i >= len(KO_NAMES) - 1:
            return "Finale"
        return f"{KO_NAMES[i]} – {'andata' if leg == 0 else 'ritorno'}"
    return f"{r}ª giornata"


def round_names(d):
    """{giornata: nome} delle partite in calendario (solo in coppa, dove i turni non sono tutti «giornate»)."""
    if not CUP:
        return {}
    rs = {e.get("round") for lst in ("played", "live", "next") for e in d.get(lst) or [] if e.get("round")}
    return {str(r): round_label(r) for r in sorted(rs)}


def cup_rounds(d):
    """Turni della Champions: la fase campionato in ordine di data (8 giornate), l'eliminazione diretta dalla fase di
    ESPN (andata e ritorno: dalla nota di ESPN o, se manca, la seconda partita tra le stesse squadre)."""
    evs = sorted({str(e["id"]): e for lst in ("played", "live", "next") for e in d.get(lst) or []}.values(), key=lambda e: e["start"])
    league = [e for e in evs if e.get("stage") in (None, "league-phase")]
    teams_in, cur = {}, 0
    for e in league:
        h, a = e["home"]["id"], e["away"]["id"]
        r = cur or 1
        if h in teams_in.get(r, set()) or a in teams_in.get(r, set()):
            r = cur + 1
        e["round"] = min(r, 8)
        cur = max(cur, r)
        teams_in.setdefault(r, set()).update((h, a))
    seen = {}
    for e in evs:
        st = e.get("stage")
        if st not in KO_STAGES:
            continue
        i = KO_STAGES.index(st)
        if st == "final":
            e["round"], e["leg"] = 9 + 2 * i, None
            continue
        pair = (st, frozenset((e["home"]["id"], e["away"]["id"])))
        leg = e.get("leg") or (2 if pair in seen and seen[pair] != e["id"] else 1)
        seen.setdefault(pair, e["id"])
        e["leg"] = leg
        e["round"] = 9 + 2 * i + (leg - 1)
    # ritorno: il risultato dell'andata, girato sulle squadre di questa partita (per la probabilità di passare il turno)
    first = {}
    for e in evs:
        if e.get("leg") == 1 and e.get("hs") is not None:
            first[(e.get("stage"), e["home"]["id"], e["away"]["id"])] = (e["hs"], e["as"])
    for e in evs:
        if e.get("leg") == 2:
            f = first.get((e.get("stage"), e["away"]["id"], e["home"]["id"]))
            e["tie"] = {"first": [f[1], f[0]]} if f else None   # gol dell'andata: [squadra di casa ora, ospite ora]
        elif e.get("stage") == "final":
            e["tie"] = {"first": [0, 0], "final": True}


def number_rounds(d):
    """Giornate quando ESPN non le dà (leghe senza dati di partenza, come la Premier League): in ordine di data, una
    giornata finisce quando una delle squadre gioca di nuovo. Le partite che hanno già la giornata la tengono."""
    evs = sorted({str(e["id"]): e for lst in ("played", "live", "next") for e in d.get(lst) or []}.values(),
                 key=lambda e: e["start"])
    teams_in, cur = {}, 0
    for e in evs:
        h, a = e["home"]["id"], e["away"]["id"]
        if not e.get("round"):
            r = cur or 1
            if h in teams_in.get(r, set()) or a in teams_in.get(r, set()):
                r = cur + 1
            e["round"] = r
        cur = max(cur, e["round"])
        teams_in.setdefault(e["round"], set()).update((h, a))


# Champions: i nomi brevi di ESPN che in italiano non si usano
CUP_NAMES = {"Inter Milan": "Inter", "AS Roma": "Roma", "S Bratislava": "Slovan Bratislava", "Bodo/Glimt": "Bodø/Glimt",
             "Atlético": "Atlético Madrid"}


def espn_team(t):
    """Squadra ESPN nel formato dell'app (per le leghe che partono da ESPN l'id è quello ESPN)."""
    name = t.get("shortDisplayName") or t.get("displayName")
    return {"id": int(t["id"]), "name": CUP_NAMES.get(name, name) if CUP else name, "fullName": t.get("displayName"),
            "code": t.get("abbreviation"), "color": "#" + (t.get("color") or "6C7A72")}


def espn_table(j, teams):
    """Classifica ESPN -> righe nel formato dell'app."""
    ch = j.get("children") or []
    rows = []
    entries = ((ch[0].get("standings") if ch else j.get("standings")) or {}).get("entries") or []
    for e in entries:
        tid = str((e.get("team") or {}).get("id"))
        if tid not in teams:
            continue
        S = {s.get("name"): s.get("value") for s in e.get("stats") or []}
        n = lambda k: int(S.get(k) or 0)
        rows.append({"team": teams[tid], "pos": n("rank"), "p": n("gamesPlayed"), "w": n("wins"), "d": n("ties"), "l": n("losses"),
                     "gf": n("pointsFor"), "ga": n("pointsAgainst"), "pts": n("points"), "zone": zone_at(n("rank"), len(entries))})
    return sorted(rows, key=lambda r: r["pos"])


async def espn_bootstrap():
    """Primo avvio di una lega nuova (es. Premier League), solo con ESPN: squadre, classifica, calendario con le
    giornate, formazioni e statistiche delle partite giocate, e la stagione scorsa (classifica, risultati, arbitri e
    cartellini). Poi l'aggiornamento normale aggiunge Understat, allenatori e probabili formazioni."""
    log(f"Primo avvio della {LEGA['name']}: scarico i dati di base da ESPN (qualche minuto)")
    sb = await espn_get(ESPN_SITE + "/scoreboard")
    y = int((((sb.get("leagues") or [{}])[0].get("season") or {}).get("year")) or time.localtime().tm_year)
    j = await espn_get(ESPN_STAND)
    ch = j.get("children") or []
    entries = ((ch[0].get("standings") if ch else j.get("standings")) or {}).get("entries") or []
    teams = {str(e["team"]["id"]): espn_team(e["team"]) for e in entries if e.get("team")}
    for tid in teams:
        ESPNMAP.setdefault("teams", {})[tid] = tid
    d = {"season": {"id": y, "year": f"{y % 100:02d}/{(y + 1) % 100:02d}"},
         "standings": {"total": espn_table(j, teams), "home": [], "away": []},
         "teams": {tid: {"team": t, "stats": {"matches": 0}} for tid, t in teams.items()},
         "players": [], "played": [], "next": [], "live": [], "updatedAt": time.time()}
    lt = time.localtime()
    upto = (lt.tm_year * 12 + lt.tm_mon) + 1
    months = [f"{yy}{mm:02d}" for yy, mm in [(y, m) for m in range(7, 13)] + [(y + 1, m) for m in range(1, 7)]
              if yy * 12 + mm <= upto or CUP]
    await espn_schedule(d, months)
    cup_rounds(d) if CUP else number_rounds(d)
    for e in [e for e in d["played"] if e.get("espn")]:
        try:
            await espn_summary(e)
        except Exception as ex:   # la riprende summaries_due al giro dopo
            log(f"Riepilogo di {e['home']['name']} - {e['away']['name']} non scaricato ({errtxt(ex)}): si riprova più tardi")
    # stagione scorsa: classifica (anche delle squadre retrocesse), poi risultati, arbitri e cartellini di ogni partita
    pj = await espn_get(ESPN_STAND, season=str(y - 1))
    pch = pj.get("children") or []
    pteams = {str(e["team"]["id"]): espn_team(e["team"])
              for e in ((pch[0].get("standings") if pch else pj.get("standings")) or {}).get("entries") or [] if e.get("team")}
    PRIOR.clear()
    PRIOR.update(year=f"{(y - 1) % 100:02d}/{y % 100:02d}", sid=y - 1, complete=True,
                 standings={"total": espn_table(pj, pteams), "home": [], "away": []})
    while not PRIOR.get("resultsDone"):
        await espn_prior_results()
    skip = set()
    while prior_ref_pending() and await prior_ref_step(40, skip):
        pass
    save_json(MATCH_FILE, MATCHES)
    save_json(ESPN_FILE, ESPNMAP)
    save_json(DATA_FILE, d)
    log(f"{LEGA['name']}: {len(teams)} squadre, {len(d['played'])} partite giocate, {len(d['next'])} da giocare, "
        f"stagione scorsa {len(PRIOR.get('results') or [])} partite")
    return d


async def espn_prior_results():
    """Risultati della stagione scorsa da ESPN (servono ai precedenti tra stili)."""
    teams = {str(r["team"]["id"]): r["team"] for r in (PRIOR.get("standings") or {}).get("total") or []}
    if not teams:
        return
    y1 = 2000 + int(str(PRIOR.get("year", "25/26"))[:2])
    months = [f"{y1}{m:02d}" for m in range(8, 13)] + [f"{y1 + 1}{m:02d}" for m in range(1, 7)]
    page = PRIOR.get("espnPage", 0)
    if page >= len(months):
        PRIOR["resultsDone"] = True
        save_json(PRIOR_FILE, PRIOR)
        return
    j = await espn_get(ESPN_SITE + "/scoreboard", dates=months[page])
    evs = [x for x in (espn_event(e, teams) for e in j.get("events", [])) if x and x["status"] == "finished"]
    for x in evs:
        x["id"] = f"p{x['espn']}"
    have = {e.get("id") for e in PRIOR.get("results") or []}
    PRIOR.setdefault("results", []).extend(x for x in evs if x["id"] not in have)
    PRIOR["espnPage"] = page + 1
    if PRIOR["espnPage"] >= len(months):
        PRIOR["resultsDone"] = True
        log(f"Risultati della stagione {PRIOR.get('year')} salvati da ESPN: {len(PRIOR['results'])} partite")
    save_json(PRIOR_FILE, PRIOR)


def in_window(d, now):
    if d.get("live"):
        return True
    return any(e.get("status") == "notstarted" and e["start"] - 300 <= now <= e["start"] + MATCH_LENGTH
               for e in d.get("next", []))


def next_kickoff(d, now):
    starts = [e["start"] - 300 for e in d.get("next", []) if e.get("status") == "notstarted" and e["start"] - 300 > now]
    return min(starts) if starts else None


# ---------- analisi (model.py) ----------

def coach_changes(d):
    """Cambi di allenatore durante la stagione in corso (non quelli d'estate), da Wikipedia in inglese:
    {id squadra: {"at": data del cambio, "pre": cambiato anche d'estate}}. Dopo un cambio le partite di prima pesano meno nella forza della squadra."""
    starts = [e["start"] for e in d.get("played") or [] if e.get("start")]
    if not starts:
        return {}
    first, out, pre = min(starts), {}, set()
    for c in EXTRA.get("wikiEn") or []:
        t = c.get("since") or c.get("left")
        tid = team_by_name(d, c.get("team"))
        if not tid or not t:
            continue
        if c.get("pre") or t <= first + 86400:
            pre.add(tid)   # cambiato anche d'estate: la stagione scorsa pesava già meno
        else:
            out[tid] = max(out.get(tid, 0), t)
    return {tid: {"at": t, "pre": tid in pre} for tid, t in out.items()}


def us_history(d):
    """Partite della stagione di ogni squadra da Understat (data, gol, xG senza rigori), per pesarle una a una."""
    u = load_json(us_file(season_year(d)), {}) or {}
    out = {}
    for t in (u.get("teams") or {}).values():
        tid = team_by_name(d, t.get("title"))
        rows = [{"t": us_time(h.get("date")), "gf": model.num(h.get("scored")) or 0, "ga": model.num(h.get("missed")) or 0,
                 "npxg": model.num(h.get("npxG")) or 0, "npxga": model.num(h.get("npxGA")) or 0} for h in t.get("history") or []]
        if tid:
            out[tid] = [r for r in rows if r["t"]]
    return out


ANALYSIS = {"key": None}


def analysis():
    d = STATE["data"]
    key = (d.get("updatedAt"), VERSION["matches"], VERSION["squads"], VERSION["coaches"], VERSION["forza"], PRIOR.get("sid"),
           len(PRIOR.get("results") or []), len(FANTA.get("teams", [])),
           sum(1 for v in (PRIOR.get("refCards") or {}).values() if "roles" in v) // 20)
    if ANALYSIS["key"] != key:
        A = model.build(d, PRIOR, MATCHES, coaches=COACHES, role_rows=role_rows(d), changes=coach_changes(d), us_hist=us_history(d),
                        ext=cup_ext(d))
        nxt = sorted((e for e in d.get("next") or [] if e.get("status") == "notstarted"
                      and str(e["home"]["id"]) in A["T"] and str(e["away"]["id"]) in A["T"]), key=lambda e: e["start"])
        # giocatori in evidenza: le partite della prossima giornata (o dei 4 giorni dopo la prima, se manca la giornata)
        same = ((lambda e: e.get("round") == nxt[0].get("round")) if nxt and nxt[0].get("round") is not None
                else (lambda e: e["start"] - nxt[0]["start"] < 4 * 86400))
        fixtures, items, every = {}, [], []
        for e in nxt:
            P = model.predict(A, e["home"]["id"], e["away"]["id"], e, MATCHES.get(str(e["id"])))
            fixtures[str(e["id"])] = model.summary(P)
            every.append((e, P))
            if same(e):
                items.append((e, P))
        # partite più gustose dei prossimi giorni: divario, squadra top contro squadra flop, giocate con valore
        pos = {str(r["team"]["id"]): r.get("pos") for r in (d.get("standings") or {}).get("total") or []}
        ANALYSIS.update(key=key, A=A, pub=model.public_analysis(A), fixtures=fixtures, evidenza=model.evidenza(items, A=A),
                        preds=items, proj=cup_projection(d, A) if CUP and A.get("cup") else None,
                        gustose=model.gustose(every, A, pos=None if CUP else pos))
    return ANALYSIS


def update_history():
    try:
        if model.update_history(HISTORY, analysis()["A"], STATE["data"], MATCHES, ids=REG["espn"]):
            save_json(HISTORY_FILE, HISTORY)
    except Exception as e:
        log(f"Storico pronostici non aggiornato: {errtxt(e)}")


# ---------- fonti di riserva (fantacalcio.it, Wikipedia, ESPN) ----------

async def web_text(url, headers=None):
    async with HTTP["web"].get(url, headers=headers, timeout=aiohttp.ClientTimeout(total=30)) as r:
        if r.status != 200:
            raise RuntimeError(f"{urlsplit(url).netloc} HTTP {r.status}")
        return await r.text()


def team_by_name(d, name):
    tk, best, bs = tokens(name), None, 0
    for r in d["standings"]["total"]:
        t = r["team"]
        sc = len(tk & tokens(t.get("name"), t.get("fullName"), t.get("shortName")))
        if sc > bs:
            best, bs = str(t["id"]), sc
    return best


def roster_cands(tid):
    cands = [p for p in STATE["data"]["players"] if str(p.get("teamId")) == str(tid)]
    have = {p["id"] for p in cands}
    cands += [{"id": int(pid), "name": x.get("name"), "pos": x.get("pos"), "minutesPlayed": 0}
              for pid, x in (SQUADS.get("players") or {}).items() if str(x.get("teamId")) == str(tid) and int(pid) not in have]
    return cands


def roster_fuzzy(name, cands):
    """Secondo tentativo per i nomi delle formazioni probabili scritti in un altro modo (15/10/2026: OneFootball scrive
    «Matvey Safonov», ESPN «Matvei Safonov», e il portiere titolare del PSG risultava assente contro il Man City;
    in Liga i nomi completi «Pablo Barrios Rivas», «Bryan Zaragoza Martinez»). Nella squadra, l'unico giocatore il cui
    nome più corto ha tutte le parole nell'altro, anche con piccole differenze («Matvey»/«Matvei», «Sam»/«Samuel»);
    se non c'è, l'unico che ha in comune una parola di almeno 4 lettere («Bote Baku» = Ridle Baku). Mai se i
    candidati sono più di uno."""
    clean = re.sub(r"\s+(?:[A-Z]\.){2,}$", "", name or "").replace("'", "")
    a = [t for t in model.norm_tokens(clean) if len(t) > 1]
    if not a:
        return None

    def fit(t, toks):   # parola uguale, quasi uguale o iniziale di almeno 3 lettere
        return any(t == u or (min(len(t), len(u)) >= 3 and (u.startswith(t) or t.startswith(u)))
                   or difflib.SequenceMatcher(None, t, u).ratio() >= .8 for u in toks)
    named = [(c, [t for t in model.norm_tokens(c.get("name")) if len(t) > 1]) for c in cands]
    hits = [c for c, b in named if b and all(fit(t, b if len(a) <= len(b) else a) for t in (a if len(a) <= len(b) else b))]
    if len(hits) == 1:
        return hits[0]
    if hits:
        return None
    share = [c for c, b in named if any(len(t) >= 4 and t in b for t in a)]
    return share[0] if len(share) == 1 else None


def fc_player(name, cands):
    """Nome di fantacalcio.it (es. "Martinez L.") o di OneFootball -> id dell'anagrafica; se non trovato, un id
    negativo stabile."""
    p = model.match_roster_player({"name": name}, cands) or roster_fuzzy(name, cands)
    return (p["id"], p.get("name") or name) if p else (-(zlib.crc32(name.encode()) % 10 ** 8), name)


def fc_side(tid, s):
    cands = roster_cands(tid)
    pos, _ = fonti.lines_positions(s["formation"], s["starters"])
    role = {"p": "G", "d": "D", "c": "M", "a": "F"}
    out = {"formation": s["formation"], "starters": [], "subs": [], "missing": [], "cautioned": []}
    for p, ps in zip(s["starters"], pos):
        pid, nm = fc_player(p["name"], cands)
        out["starters"].append({"id": pid, "name": nm, "pos": ps, "pct": p["pct"]})
    for p in s["bench"]:
        pid, nm = fc_player(p["name"], cands)
        out["subs"].append({"id": pid, "name": nm, "pos": role.get(p["role"]), "pct": p["pct"]})
    for key, typ, reason, label in (("suspended", "missing", 3, "Squalificato"), ("injured", "missing", 1, "Infortunato"),
                                    ("doubtful", "doubtful", None, "In dubbio")):
        for m in s.get(key) or []:
            pid, nm = fc_player(m["name"], cands)
            out["missing"].append({"id": pid, "name": nm, "type": typ, "reason": reason, "desc": m.get("desc") or label})
    out["cautioned"] = [fc_player(m["name"], cands)[1] for m in s.get("cautioned") or []]
    return out


def of_side(tid, s):
    """Formazione probabile di OneFootball nel formato dell'app (senza percentuali e indisponibili)."""
    cands = roster_cands(tid)
    pos, _ = fonti.lines_positions(s["formation"], s["starters"])
    out = {"formation": s["formation"], "starters": [], "subs": [], "missing": [], "cautioned": []}
    for p, ps in zip(s["starters"], pos):
        pid, nm = fc_player(p["name"], cands)
        out["starters"].append({"id": pid, "name": nm, "pos": ps})
    return out


PHOTO_EVERY = 86400   # rose di OneFootball per le foto: una volta al giorno (20 pagine)


def of_team(d, slug):
    """Squadra della lega da un indirizzo di OneFootball («manchester-city-209»), solo se il nome corrisponde bene
    (le pagine citano anche squadre di altre competizioni: «west-ham-united» non è il Manchester United)."""
    words = tokens(" ".join(w for w in slug.split("-") if not w.isdigit()))
    tid = team_by_name(d, " ".join(words))
    if not tid or not words:
        return None
    t = next((r["team"] for r in d["standings"]["total"] if str(r["team"]["id"]) == tid), {})
    have = tokens(t.get("name"), t.get("fullName"), t.get("shortName"))
    return tid if len(words & have) / len(words) >= .5 else None


async def of_photos_step(d, now):
    """Foto dei giocatori (solo per la pagina del Mac): dalle rose di OneFootball, una volta al giorno. A ogni
    giocatore dell'anagrafica va l'id OneFootball di chi ha lo stesso cognome nella stessa squadra."""
    if CLOUD or not LEGA.get("of_comp") or now - EXTRA.get("photoAt", 0) < PHOTO_EVERY:
        return
    EXTRA["photoAt"] = now - PHOTO_EVERY + 6 * 3600   # se va male, si riprova tra 6 ore
    save_json(EXTRA_FILE, EXTRA)
    teams = {}
    for slug in fonti.parse_of_teams(await web_text(fonti.OF_TABLE.format(lega=LEGA["of_comp"]))):
        tid = of_team(d, slug)
        if tid and tid not in teams:
            teams[tid] = slug
    n = 0
    for tid, slug in teams.items():
        squad = fonti.parse_of_squad(await web_text(fonti.OF_SQUAD.format(team=slug)))
        mine = [(cid, x) for cid, x in REG["info"].items() if str(x.get("teamId")) == tid]
        for name, ofid in squad:
            best = max(((reg_score(name, x), cid) for cid, x in mine), default=(0, None))
            if best[0] >= 4 and REG["info"][best[1]].get("ofId") != ofid:
                REG["info"][best[1]]["ofId"] = ofid
                IMG_MISSING.discard(f"player-{best[1]}")
                n += 1
    save_json(REG_FILE, REG)
    EXTRA["photoAt"] = now
    save_json(EXTRA_FILE, EXTRA)
    log(f"Foto dei giocatori (OneFootball): {len(teams)} squadre, {n} giocatori collegati")


async def onefootball_step(d, now):
    """Probabili formazioni da OneFootball, per le leghe senza Fantacalcio.it, nella settimana prima delle partite.
    Le ufficiali arrivano poi da ESPN circa un'ora prima, e prendono il loro posto."""
    nxt = [e for e in d.get("next") or [] if e.get("status") == "notstarted" and 0 < e["start"] - now <= 6 * 86400]
    if not nxt or now - EXTRA.get("ofAt", 0) < FC_NEAR:
        return
    EXTRA["ofAt"] = now - FC_NEAR + 900   # se va male, si riprova tra un quarto d'ora
    save_json(EXTRA_FILE, EXTRA)
    ids = fonti.parse_of_fixtures(await web_text(fonti.OF_FIXTURES.format(lega=LEGA["onefootball"])))
    n = 0
    for mid in ids[:len(nxt) + 4]:
        try:
            m = fonti.parse_of_match(await web_text(fonti.OF_MATCH.format(id=mid)))
        except RuntimeError:
            continue
        if not m:
            continue
        hid, aid = team_by_name(d, m["home"]), team_by_name(d, m["away"])
        e = next((e for e in nxt if str(e["home"]["id"]) == hid and str(e["away"]["id"]) == aid), None)
        x = match_entry(e) if e else None
        if not x or (x.get("lineups") or {}).get("confirmed"):
            continue
        x["lineups"] = {"confirmed": False, "source": "onefootball", "updated": now,
                        "home": of_side(hid, m["lineups"]["home"]), "away": of_side(aid, m["lineups"]["away"])}
        n += 1
    if n:
        VERSION["matches"] += 1
        save_json(MATCH_FILE, MATCHES)
        log(f"Probabili formazioni (OneFootball): {n} partite")
    EXTRA["ofAt"] = now
    save_json(EXTRA_FILE, EXTRA)


async def fantacalcio_step(d, now):
    """Probabili formazioni e indisponibili da fantacalcio.it, nella settimana prima delle partite."""
    nxt = [e for e in d.get("next") or [] if e.get("status") == "notstarted"]
    if not nxt:
        return
    h = min((e["start"] - now) / 3600 for e in nxt)
    if h > 6 * 24 or now - EXTRA.get("fcAt", 0) < (FC_NEAR if h <= 48 else FC_FAR):
        return
    EXTRA["fcAt"] = now - (FC_NEAR if h <= 48 else FC_FAR) + 900   # se va male, si riprova tra un quarto d'ora
    save_json(EXTRA_FILE, EXTRA)
    found = fonti.parse_probabili(await web_text(fonti.FC_PROBABILI))
    n = 0
    for m in found:
        hid, aid = team_by_name(d, m["home"]["team"]), team_by_name(d, m["away"]["team"])
        e = next((e for e in nxt if str(e["home"]["id"]) == hid and str(e["away"]["id"]) == aid), None)
        if not e:
            continue
        x = match_entry(e)
        if (x.get("lineups") or {}).get("confirmed"):
            continue
        x["lineups"] = {"confirmed": False, "source": "fantacalcio", "updated": m.get("updated"),
                        "home": fc_side(hid, m["home"]), "away": fc_side(aid, m["away"])}
        n += 1
    if n:
        VERSION["matches"] += 1
        save_json(MATCH_FILE, MATCHES)
        log(f"Probabili formazioni e indisponibili (fantacalcio.it): {n} partite")
    EXTRA["fcAt"] = STATUS["fcAt"] = now
    save_json(EXTRA_FILE, EXTRA)


def ref_full_name(surname):
    """Cognome dell'arbitro (fantacalcio.it) -> nome completo con cui compare nelle partite ESPN, per collegarlo ai
    suoi cartellini. Se nessuno o più arbitri hanno quel cognome resta il cognome."""
    tk = tokens(surname)
    names = [(x.get("referee") or {}).get("name") for x in MATCHES.values()]
    names += [v.get("ref") for v in (PRIOR.get("refCards") or {}).values()]
    hits = {frozenset(tokens(n)): n for n in names if n and tk and tk < tokens(n)}
    return next(iter(hits.values())) if len(hits) == 1 else surname


async def fc_prior_referees(d, now):
    """Una volta sola, 10 giornate a ogni giro: l'arbitro di ogni partita della scorsa stagione da fantacalcio.it.
    ESPN lo riporta solo in poche partite (30 su 380 nel 2025/26) ma ha tutti i cartellini: insieme danno la
    severità di ogni arbitro su una stagione intera, invece che sulle 1-4 partite di quest'anno."""
    rc = PRIOR.get("refCards") or {}
    y = re.fullmatch(r"(\d\d)/(\d\d)", PRIOR.get("year") or "")
    done = PRIOR.setdefault("refFc", {}).setdefault("rounds", [])
    if not y or not rc or len(done) >= 38 or in_window(d, now):
        return
    season = f"20{y.group(1)}-{y.group(2)}"
    same = lambda a, b: bool(tokens(a) & tokens(b))

    async def page(rnd, mid):
        try:
            return fonti.parse_partita_fc(await web_text(fonti.FC_PARTITA.format(giornata=rnd, stagione=season, id=mid)))
        except RuntimeError:
            return None

    n = 0
    for rnd in [r for r in range(1, 39) if r not in done][:10]:
        first = fonti.parse_id_partita_fc(await web_text(fonti.FC_CALENDARIO.format(giornata=f"{rnd}/{season}")), rnd, season)
        found = []
        if first:   # gli id delle 10 partite della giornata sono consecutivi: si va avanti e indietro finché ci sono
            for step in (1, -1):
                mid = first if step == 1 else first - 1
                while len(found) < 10 and (p := await page(rnd, mid)):
                    found.append(p)
                    mid += step
        for home, away, ref in found:
            x = next((x for x in PRIOR.get("results") or [] if same(home, x["home"]["name"]) and same(away, x["away"]["name"])), None)
            e = rc.get(str((x or {}).get("espn")))
            if ref and e is not None and not e.get("ref"):
                e["ref"] = ref
                n += 1
        if found:   # se la pagina è cambiata e non si trova niente, si riprova al giro dopo
            done.append(rnd)
    save_json(PRIOR_FILE, PRIOR)
    if n:
        log(f"Arbitri della scorsa stagione (fantacalcio.it): {n} partite, giornate fatte {len(done)}/38")


async def fc_referees(d, now):
    """Arbitri designati da fantacalcio.it (pagina di ogni partita): escono 2-3 giorni prima, mentre ESPN li mette
    solo il giorno della partita. Si cercano per le partite dei prossimi 4 giorni che non hanno ancora l'arbitro."""
    todo = [e for e in d.get("next") or [] if e.get("status") == "notstarted" and 0 < e["start"] - now <= 4 * 86400
            and not ((MATCHES.get(str(e["id"])) or {}).get("referee") or {}).get("name") and e.get("round")]
    if not todo or now - EXTRA.get("refAt", 0) < NEWS_EVERY:
        return
    EXTRA["refAt"] = now
    save_json(EXTRA_FILE, EXTRA)
    n = 0
    for rnd in sorted({e["round"] for e in todo}):
        links = fonti.parse_calendario_fc(await web_text(fonti.FC_CALENDARIO.format(giornata=rnd)))
        for e in (e for e in todo if e["round"] == rnd):
            hid, aid = str(e["home"]["id"]), str(e["away"]["id"])
            url = next((u for sl, u in links for i in range(1, sl.count("-") + 1)
                        if team_by_name(d, " ".join(sl.split("-")[:i])) == hid
                        and team_by_name(d, " ".join(sl.split("-")[i:])) == aid), None)
            if not url:
                continue
            ref = fonti.parse_arbitro_fc(await web_text(url))
            if not ref:   # le designazioni escono tutte insieme: se manca in una partita, manca in tutte
                break
            name = ref_full_name(ref)
            match_entry(e)["referee"] = {"name": name}
            n += 1
            log(f"Arbitro designato (fantacalcio.it): {name} per {e['home']['name']} - {e['away']['name']}")
    if n:
        apply_ref_stats(d)
        VERSION["matches"] += 1
        save_json(MATCH_FILE, MATCHES)


async def wiki_en_changes(year):
    """Cambi di allenatore della stagione da Wikipedia in inglese (sezione «Managerial changes»)."""
    base = {"action": "parse", "page": fonti.WIKI_EN_TITLE.format(a=year, b=(year + 1) % 100), "format": "json",
            "formatversion": "2"}
    get = lambda **p: web_text(fonti.WIKI_EN + "?" + urlencode(dict(base, **p)), headers={"User-Agent": WIKI_UA})
    secs = json.loads(await get(prop="sections")).get("parse", {}).get("sections") or []
    sec = next((s["index"] for s in secs if "managerial" in s["line"].lower()), None)
    if not sec:
        return []
    return fonti.parse_cambi_en(json.loads(await get(prop="text", section=sec))["parse"]["text"])


async def wiki_table(year):
    # Wikipedia respinge i finti browser che arrivano dai computer di GitHub: vuole un programma che dica chi è
    if LEGA["dir"]:   # fuori dalla Serie A: la tabella «Personnel and kits» della Wikipedia in inglese
        base = {"action": "parse", "page": fonti.WIKI_EN_TITLE.format(a=year, b=(year + 1) % 100), "format": "json",
                "formatversion": "2"}
        get = lambda **p: web_text(fonti.WIKI_EN + "?" + urlencode(dict(base, **p)), headers={"User-Agent": WIKI_UA})
        secs = json.loads(await get(prop="sections")).get("parse", {}).get("sections") or []
        sec = next((s["index"] for s in secs if "personnel" in s["line"].lower()), None)
        return fonti.parse_personale_en(json.loads(await get(prop="text", section=sec))["parse"]["text"]) if sec else {}
    return fonti.parse_allenatori(await web_text(fonti.WIKI.format(a=year, b=year + 1), headers={"User-Agent": WIKI_UA}))


SCORERS_FILE = CACHE / "marcatori.json"   # classifica marcatori di Wikipedia in inglese, seconda fonte per i gol
SCORERS_EVERY = 6 * 3600


async def wiki_scorers_step(d, now):
    """Classifica marcatori della stagione da Wikipedia in inglese («Top goalscorers»): una seconda fonte per i gol,
    anche dove non ci sono né Understat né Opta (Eredivisie, Portogallo, Turchia, Champions). Ogni 6 ore."""
    if now - EXTRA.get("scorersAt", 0) < SCORERS_EVERY:
        return
    EXTRA["scorersAt"] = now - SCORERS_EVERY + 1800   # se va male, si riprova tra mezz'ora
    save_json(EXTRA_FILE, EXTRA)
    y = season_year(d)
    title = (f"{y}–{(y + 1) % 100:02d} UEFA Champions League" if CUP
             else fonti.WIKI_EN_TITLE.format(a=y, b=(y + 1) % 100))
    base = {"action": "parse", "page": title, "format": "json", "formatversion": "2"}
    get = lambda **p: web_text(fonti.WIKI_EN + "?" + urlencode(dict(base, **p)), headers={"User-Agent": WIKI_UA})
    secs = json.loads(await get(prop="sections")).get("parse", {}).get("sections") or []
    sec = next((x["index"] for x in secs if "scorer" in x["line"].lower()), None)
    rows = fonti.parse_marcatori_en(json.loads(await get(prop="text", section=sec))["parse"]["text"]) if sec else []
    save_json(SCORERS_FILE, {"at": now, "page": title, "rows": rows})
    EXTRA["scorersAt"] = now
    save_json(EXTRA_FILE, EXTRA)


SRC_NAMES = {"srcUs": "Understat", "srcOpta": "Opta", "srcFc": "Fantacalcio.it", "srcUefa": "UEFA"}
SRC_KEYS = (("minuti", 45), ("gol", 0), ("assist", 1), ("gialli", 0), ("rossi", 0))   # nome e tolleranza


def sources_compare(d):
    """Seconda fonte per i numeri base dei giocatori: minuti, gol, assist e cartellini dei tabellini ESPN contro
    Understat, Opta, Fantacalcio.it (Serie A), la UEFA (Champions) e la classifica marcatori di Wikipedia. Gol e
    cartellini devono essere uguali, gli assist entro 1 (le fonti li contano in modo diverso), i minuti entro 45.
    Chi ha giocato nelle ultime 36 ore non si confronta: Opta e Wikipedia si aggiornano dopo.
    -> {"at", "sources": [{"src", "n" (giocatori confrontati), "same", "nDiff", "diff": [...]}]}"""
    now = time.time()
    recent = set()
    for e in d.get("played") or []:
        if now - e["start"] < 36 * 3600:
            for pid in (((MATCHES.get(str(e["id"])) or {}).get("box") or {}).get("players") or {}):
                if REG["espn"].get(str(pid)) is not None:
                    recent.add(str(REG["espn"][str(pid)]))
    uefa = uefa_players(d) if CUP else {}
    players = [p for p in d.get("players") or [] if p.get("minutesEspn") is not None and str(p["id"]) not in recent]
    out = []
    for key, name in SRC_NAMES.items():
        if key == "srcUs" and SHOT_XG:   # lì i dati «Understat» li fa l'app con ESPN: non sono un'altra fonte
            continue
        n = same = 0
        diff = []
        for p in players:
            u = uefa.get(str(p["id"])) if key == "srcUefa" else None
            other = [u.get("min"), u.get("g"), u.get("a"), None, None] if u else p.get(key)
            if not other:
                continue
            espn = [p.get("minutesEspn"), p.get("goalsEspn"), p.get("assistsEspn"), p.get("yellowCardsEspn"), p.get("redCardsEspn")]
            bad = [[lab, espn[i], other[i]] for i, (lab, tol) in enumerate(SRC_KEYS)
                   if espn[i] is not None and other[i] is not None and abs(espn[i] - other[i]) > tol]
            n += 1
            if bad:
                diff.append({"id": p["id"], "name": p.get("name"), "team": str(p.get("teamId")), "d": bad})
            else:
                same += 1
        if n:
            out.append({"src": name, "n": n, "same": same, "nDiff": len(diff), "diff": diff[:40]})
    # classifica marcatori di Wikipedia: solo i gol, solo chi c'è in classifica
    wk = load_json(SCORERS_FILE, {}) or {}
    byid = {str(p["id"]): p for p in players}
    n = same = 0
    diff = []
    for name, club, goals in wk.get("rows") or []:
        tid = team_by_name(d, club)
        cid = reg_find(name, [tid]) if tid else None
        p = byid.get(str(cid)) if cid else None
        if not p:
            continue
        n += 1
        if (p.get("goalsEspn") or 0) != goals:
            diff.append({"id": p["id"], "name": p.get("name"), "team": str(p.get("teamId")), "d": [["gol", p.get("goalsEspn"), goals]]})
        else:
            same += 1
    if n:
        out.append({"src": "Wikipedia (marcatori)", "n": n, "same": same, "nDiff": len(diff), "diff": diff[:40]})
    return {"at": now, "sources": out, "recent": len(recent)}


async def wiki_coaches(d, now):
    """Allenatori da Wikipedia, con le giornate in panchina (anche quelli della scorsa stagione)."""
    if now - EXTRA.get("wikiAt", 0) < WIKI_EVERY and EXTRA.get("wikiCur"):
        return
    EXTRA["wikiAt"] = now - WIKI_EVERY + 900   # se va male, si riprova tra un quarto d'ora
    save_json(EXTRA_FILE, EXTRA)
    y = 2000 + int(str((d.get("season") or {}).get("year") or "26/27")[:2])
    cur = await wiki_table(y)
    prev = EXTRA.get("wikiPrev")
    if not prev or not all(isinstance(v, list) for v in prev.values()):
        prev = EXTRA["wikiPrev"] = await wiki_table(y - 1)
    try:
        EXTRA["wikiEn"] = await wiki_en_changes(y)
        STATUS.pop("err_Wikipedia inglese", None)
    except Exception as e:
        STATUS["err_Wikipedia inglese"] = errtxt(e)[:200]
        log(f"Errore Wikipedia inglese: {errtxt(e)}")
    en = EXTRA.get("wikiEn") or []
    n = 0
    for team, ten in cur.items():
        tid = team_by_name(d, team)
        if not tid or not ten:
            continue
        # vince la Wikipedia che sa del cambio più recente; se è andato via e non c'è ancora il successore,
        # la panchina resta "da nominare"
        coach, left = fonti.allenatore_attuale(ten, [c for c in en if team_by_name(d, c["team"]) == tid])
        before = next((v[-1]["name"] for k, v in prev.items() if v and tokens(k) & tokens(team)), None)
        c = COACHES.setdefault(tid, {})
        old = (c.get("wiki") or {}).get("name")
        if left and old:
            log(f"{team}: {left['name']} ha lasciato la panchina, nuovo allenatore non ancora annunciato")
        elif coach and old and tokens(old) != tokens(coach):
            log(f"Cambio di allenatore ({team}): {coach} al posto di {old}")
        c["wiki"] = {"name": coach, "new": (tokens(before) != tokens(coach)) if before and coach else None, "left": left}
        c["manager"] = {"id": None, "name": coach} if coach else None
        n += 1
    if n:
        EXTRA["wikiCur"] = cur
        save_json(COACH_FILE, COACHES)
        VERSION["coaches"] += 1
        EXTRA["wikiAt"] = now
        save_json(EXTRA_FILE, EXTRA)


def same_ref(a, b):
    """Stesso arbitro: il nome più corto sta nell'altro, con le parole di seguito e nello stesso ordine (fantacalcio.it
    dà solo il cognome, ESPN nome e cognome). Con le sole parole in comune «Di Marco» risultava uguale a «Marco Di
    Bello» (corretto il 23/10/2026)."""
    sa, sb = tok_seq(a), tok_seq(b)
    if not sa or not sb:
        return False
    short, long_ = sorted((sa, sb), key=len)
    return any(long_[i:i + len(short)] == short for i in range(len(long_) - len(short) + 1))


REF_OTHER = {"at": 0, "rows": []}


def other_ref_rows():
    """In coppa: arbitro e cartellini delle partite dei campionati che l'app segue (questa stagione e la scorsa), con la
    media di gialli di quel campionato in quella stagione. Gli arbitri della Champions dirigono soprattutto lì: con le
    sole partite di coppa ne avrebbero una o due. Si rilegge ogni 6 ore (anche su GitHub ci sono i dati di tutte le
    leghe: la Champions si aggiorna per ultima)."""
    if time.time() - REF_OTHER["at"] < 6 * 3600:
        return REF_OTHER["rows"]
    rows = []
    for k, L in LEGHE.items():
        if k == LEGA_KEY:
            continue
        base = (DATA_BASE / L["dir"] if L["dir"] else DATA_BASE) / "cache"
        cur = [((x.get("referee") or {}).get("name"), x.get("cards")) for x in (load_json(base / "matches.json", {}) or {}).values()]
        prev = [(v.get("ref"), v.get("cards")) for v in ((load_json(base / "prior.json", {}) or {}).get("refCards") or {}).values()]
        for season, items in (("cur", cur), ("prev", prev)):
            items = [(n, c) for n, c in items if n and c]
            if items:
                avg = sum(c["y"] for _, c in items) / len(items)
                rows += [(n, c, season, avg, L["name"]) for n, c in items]
    REF_OTHER.update(at=time.time(), rows=rows)
    return rows


def ref_stats(name, teams=None):
    """Statistiche di un arbitro dalle partite di questa stagione e della scorsa: cartellini da ESPN, arbitro da ESPN
    o, per la scorsa stagione, da fantacalcio.it. In coppa anche le sue partite nei campionati che l'app segue
    (other_ref_rows): il termine di paragone (base) è allora la media di gialli dei campionati di ogni sua partita,
    così un arbitro della Liga non sembra severo solo perché in Liga i gialli sono di più. Con i risultati delle sue
    partite (ref_results; teams: le due squadre della partita che arbitra)."""
    g = y = r = 0
    rows = [((x.get("referee") or {}).get("name"), x.get("cards"), "cur") for x in MATCHES.values()]
    rows += [(v.get("ref"), v.get("cards"), "prev") for v in (PRIOR.get("refCards") or {}).values()]
    # termine di paragone: i gialli a partita di tutte le partite da cui vengono i dati degli arbitri (scorsa stagione e
    # questa). Con la media di quest'anno sembravano tutti severi: la stagione scorsa ne aveva di più (3,59 contro 3,22)
    cards = [c["y"] for _, c, _ in rows if c]
    own = sum(cards) / len(cards) if cards else None
    rows = [(rn, c, season, own, None) for rn, c, season in rows]
    if CUP:
        rows += other_ref_rows()
    split = {"prev": [0, 0], "cur": [0, 0]}   # [partite, gialli] della scorsa stagione e di questa
    bsum, dom = 0.0, collections.Counter()
    for rn, c, season, avg, lg in rows:
        if rn and c and same_ref(rn, name) and avg:
            g, y, r = g + 1, y + c["y"], r + c["r"]
            bsum += avg
            split[season][0] += 1
            split[season][1] += c["y"]
            if lg:
                dom[lg] += 1
    base = round(bsum / g, 3) if g else None
    res = ref_results(name, teams)
    return {"name": name, "yellow": y, "red": r, "yellowRed": 0, "games": g, "source": "espn", "base": base,
            "seasons": split, **({"dom": dict(dom)} if dom else {}), **res} if g else dict({"name": name}, **res)


def ref_results(name, teams=None):
    """Risultati delle partite dell'arbitro in questa competizione, stagione in corso e scorsa (per le chicche):
    {"res": {"n", "h", "d", "a", "base": quote di vittorie in casa, pareggi e vittorie fuori di tutte le partite con
    l'arbitro noto}, "tm": {squadra: [vittorie, pareggi, sconfitte]} delle squadre teams}."""
    played = {str(e["id"]): e for e in (STATE.get("data") or {}).get("played") or [] if e.get("hs") is not None}
    prior = {str(e.get("espn")): e for e in PRIOR.get("results") or [] if e.get("hs") is not None and e.get("espn")}
    rows = [((x.get("referee") or {}).get("name"), played.get(eid)) for eid, x in MATCHES.items()]
    rows += [(v.get("ref"), prior.get(str(k))) for k, v in (PRIOR.get("refCards") or {}).items()]
    rows = [(rn, e) for rn, e in rows if rn and e]
    if not rows:
        return {}
    out = lambda e: "h" if e["hs"] > e["as"] else "a" if e["as"] > e["hs"] else "d"
    pool = collections.Counter(out(e) for _, e in rows)
    mine = [e for rn, e in rows if same_ref(rn, name)]
    c = collections.Counter(out(e) for e in mine)
    tm = {}
    for e in mine:
        for side, k in (("home", "h"), ("away", "a")):
            tid = str(e[side]["id"])
            if teams is None or tid in teams:
                r = tm.setdefault(tid, [0, 0, 0])
                r[0 if out(e) == k else 1 if out(e) == "d" else 2] += 1
    return {"res": {"n": len(mine), "h": c["h"], "d": c["d"], "a": c["a"],
                    "base": [round(pool[k] / len(rows), 3) for k in ("h", "d", "a")]}, "tm": tm} if mine else {}


def apply_ref_stats(d):
    for e in (d.get("next") or []) + (d.get("live") or []):
        x = MATCHES.get(str(e["id"])) or {}
        ref = x.get("referee") or {}
        if ref.get("name") and (not ref.get("games") or ref.get("source") == "espn"):
            new = ref_stats(ref["name"], (str(e["home"]["id"]), str(e["away"]["id"])))
            if new != ref:
                x["referee"] = new
                VERSION["matches"] += 1


async def espn_prematch(d, now, limit):
    """Nei 3 giorni prima: precedenti tra le squadre e arbitro designato, dal riepilogo ESPN."""
    done = 0
    for e in d.get("next") or []:
        if done >= limit:
            break
        x = MATCHES.get(str(e["id"])) or {}
        h = (e["start"] - now) / 3600
        odds_old = now - ((x.get("odds") or {}).get("at") or 0) > 3 * 3600
        if (e.get("status") != "notstarted" or not e.get("espn") or not 1.5 < h <= 72
                or now - x.get("preAt", 0) < PRE_EVERY
                or (x.get("h2h") and (x.get("referee") or {}).get("name") and not odds_old)):
            continue
        j = await espn_get(ESPN_SITE + "/summary", event=e["espn"])
        x = match_entry(e)
        x["preAt"] = now
        keep_odds(x, e, j)
        done += 1
        games = fonti.espn_h2h(j)
        if games and not x.get("h2h"):
            ids = ESPNMAP.get("teams") or {}
            home, away = str(e["home"]["id"]), str(e["away"]["id"])
            w = {"home": 0, "draws": 0, "away": 0}
            for eh, ea, gh, ga in games:
                win = eh if gh > ga else ea if ga > gh else None
                w["draws" if win is None else "home" if str(ids.get(win)) == home else "away"] += 1
            x["h2h"] = {"team": w, "manager": None, "games": len(games), "source": "espn"}
        ref = fonti.espn_referee(j)
        if ref and tokens((x.get("referee") or {}).get("name")) != tokens(ref):
            x["referee"] = {"name": ref}
            log(f"Arbitro designato (ESPN): {ref} per {e['home']['name']} - {e['away']['name']}")
    return done


async def prior_ref_step(limit, skip=None):
    """Arbitro e cartellini delle partite della scorsa stagione (una volta sola, poco alla volta). Una partita che non
    risponde si salta (skip) e si riprova più tardi: un solo riepilogo lento non deve fermare tutto. -> scaricate."""
    rc = PRIOR.setdefault("refCards", {})
    skip = skip if skip is not None else set()
    todo = [x["espn"] for x in PRIOR.get("results") or []
            if x.get("espn") and "box" not in rc.get(str(x["espn"]), {}) and str(x["espn"]) not in skip][:limit]
    n = 0
    for eid in todo:
        try:
            j = await espn_get(ESPN_SITE + "/summary", event=eid)
        except Exception as e:
            skip.add(str(eid))
            log(f"Riepilogo ESPN {eid} della stagione scorsa non scaricato ({errtxt(e)}): si riprova più tardi")
            continue
        rc[str(eid)] = {"ref": fonti.espn_referee(j), "cards": fonti.espn_cards(j), "roles": match_roles(j) or {},
                        "box": statistiche.box_from_summary(j) or {}}
        if ESPN_XG:   # tiri della cronaca (con gli xG dalla posizione), per gli xG della stagione scorsa
            rc[str(eid)]["shots"] = {s: [x[:8] for x in v] for s, v in letture.us_like(letture.parse_espn(j)["ev"]).items()}
        n += 1
    if n:
        save_json(PRIOR_FILE, PRIOR)
    return n


def prior_ref_pending():
    rc = PRIOR.get("refCards") or {}
    return PRIOR.get("resultsDone") and any(x.get("espn") and "box" not in rc.get(str(x["espn"]), {})
                                            for x in PRIOR.get("results") or [])


def role_rows(d):
    """Gol e assist per ruolo di ogni squadra in ogni partita, con l'allenatore che era in panchina
    (giornate da Wikipedia): servono a capire quali ruoli valorizza ogni allenatore."""
    rows = []
    cur, prev = EXTRA.get("wikiCur") or {}, EXTRA.get("wikiPrev") or {}
    ten_of = lambda table, name: next((v for k, v in table.items() if isinstance(v, list) and tokens(k) & tokens(name)), None)
    names = {str(r["team"]["id"]): r["team"]["name"] for r in d["standings"]["total"]}
    for e in d.get("played") or []:
        ro = (MATCHES.get(str(e["id"])) or {}).get("roles")
        for side in ("home", "away"):
            if ro and ro.get(side):
                tid = str(e[side]["id"])
                coach = fonti.coach_at(ten_of(cur, names.get(tid, "")), e.get("round"))
                gf, ga = (e.get("hs"), e.get("as")) if side == "home" else (e.get("as"), e.get("hs"))
                rows.append(dict(ro[side], coach=coach, team=names.get(tid), season="cur", gf=gf, ga=ga, start=e["start"]))
    pnames = {str(r["team"]["id"]): r["team"]["name"] for r in (PRIOR.get("standings") or {}).get("total") or []}
    rc, count = PRIOR.get("refCards") or {}, {}
    for x in sorted(PRIOR.get("results") or [], key=lambda x: x["start"]):
        ro = (rc.get(str(x.get("espn"))) or {}).get("roles")
        for side in ("home", "away"):
            tid = str(x[side]["id"])
            count[tid] = count.get(tid, 0) + 1   # la n-esima partita della squadra: la giornata (quasi sempre)
            if ro and ro.get(side):
                name = pnames.get(tid) or x[side].get("name", "")
                gf, ga = (x.get("hs"), x.get("as")) if side == "home" else (x.get("as"), x.get("hs"))
                rows.append(dict(ro[side], coach=fonti.coach_at(ten_of(prev, name), count[tid]), team=name, season="prior",
                                 gf=gf, ga=ga, start=x["start"]))
    return rows


# ---------- statistiche di squadre e giocatori (ESPN, Understat, Fantacalcio.it) ----------

def season_year(d):
    return 2000 + int(str((d.get("season") or {}).get("year") or "26/27")[:2])


def us_file(year):
    return CACHE / f"understat-{year}.json"


async def us_get(year):
    headers = {"X-Requested-With": "XMLHttpRequest", "Referer": statistiche.UNDERSTAT_REF.format(year=year)}
    async with HTTP["web"].get(statistiche.UNDERSTAT.format(year=year), headers=headers,
                               timeout=aiohttp.ClientTimeout(total=40)) as r:
        if r.status != 200:
            raise RuntimeError(f"Understat HTTP {r.status}")
        return json.loads(await r.text())


US_MATCH = "https://understat.com/getMatchData/{id}"


def us_time(x):
    try:
        return datetime.strptime(x, "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc).timestamp()
    except (TypeError, ValueError):
        return None


def us_match_id(d, e, dates):
    """Partita di Understat che corrisponde a una partita giocata: stesse squadre, stesso giorno (orari in UTC)."""
    h, a = str(e["home"]["id"]), str(e["away"]["id"])
    for x in dates:
        t = us_time(x.get("datetime"))
        if not x.get("isResult") or t is None or abs(t - e["start"]) > 36 * 3600:
            continue
        if team_by_name(d, (x.get("h") or {}).get("title")) == h and team_by_name(d, (x.get("a") or {}).get("title")) == a:
            return x["id"]
    return None


def us_ppda(d, u, e):
    """Pressing (PPDA: passaggi concessi per ogni intervento difensivo) e passaggi vicino all'area (deep) delle due
    squadre in quella partita, da Understat."""
    out = {}
    for t in (u.get("teams") or {}).values():
        tid = team_by_name(d, t.get("title"))
        side = "home" if tid == str(e["home"]["id"]) else "away" if tid == str(e["away"]["id"]) else None
        for x in (t.get("history") or []) if side else []:
            ts = us_time(x.get("date"))
            if ts is not None and abs(ts - e["start"]) <= 36 * 3600 and x.get("h_a") == side[0]:
                pp = x.get("ppda") or {}
                out[side] = {"ppda": round(pp.get("att", 0) / max(1, pp.get("def") or 1), 2), "deep": x.get("deep")}
    return out


def us_rosters(j):
    """Formazioni di una partita su Understat: {"home"/"away": [[id Understat, minuti, gol, assist, gialli, rossi]]}."""
    num = lambda v: int(float(v or 0))
    return {side: [[str(r.get("player_id")), num(r.get("time")), num(r.get("goals")), num(r.get("assists")),
                    num(r.get("yellow_card")), num(r.get("red_card"))]
                   for r in ((j.get("rosters") or {}).get(k) or {}).values() if num(r.get("time")) > 0]
            for k, side in (("h", "home"), ("a", "away"))}


def us_links_by_minutes(d):
    """Understat -> anagrafica senza guardare i nomi: per ogni giocatore di Understat, il giocatore ESPN della stessa
    squadra con gli stessi minuti partita per partita (le due fonti differiscono di 1-3 minuti di recupero), e quando
    i minuti non bastano (due difensori sempre in campo 90') con gol e cartellini; il nome solo come spareggio. Un
    giocatore che gioca quando l'altro non c'è non è lui. -> {id Understat: id dell'anagrafica}, solo i casi sicuri."""
    apps, team_games, espn = {}, {}, {}
    for e in d.get("played") or []:
        x = MATCHES.get(str(e["id"])) or {}
        usr, box = x.get("usr"), (x.get("box") or {}).get("players") or {}
        if not usr or not box:
            continue
        for side in ("home", "away"):
            key = (str(e["id"]), side)
            team_games.setdefault(str(e[side]["id"]), []).append(key)
            espn[key] = {str(pid): p for pid, p in box.items() if p.get("side") == side and (p.get("min") or 0) > 0}
            for r in usr.get(side) or []:
                apps.setdefault(r[0], []).append((key, str(e[side]["id"]), r))
    names = {str(u.get("usId")): u.get("name") for u in (statistiche.understat_parse(load_json(us_file(season_year(d)), {})) or {}).get("players") or []}
    out = {}
    for uid, rows in apps.items():
        teams = {t for _, t, _ in rows}
        mine = {k for k, _, _ in rows}
        if len(rows) < 3:   # con una o due partite basta una coincidenza di minuti (14/10: Schuster preso per Schade)
            continue
        score, agree = {}, {}
        for pid in {pid for key, _, _ in rows for pid in espn[key]}:
            sc, ag = 0.0, 0
            for key, _, r in rows:
                p = espn[key].get(pid)
                if not p:   # non ha giocato quando il giocatore di Understat c'era
                    sc -= 2.0
                    continue
                dm = abs((p.get("min") or 0) - r[1])
                same = (p.get("goals") or 0) == r[2] and (p.get("yc") or 0) == r[4] and (p.get("rc") or 0) == r[5]
                if dm <= 4:
                    ag += 1
                sc += (1.25 if same else .25) if dm <= 4 else -2.0 if dm > 10 else 0.0
            for t in teams:   # ha giocato quando il giocatore di Understat non c'era
                sc -= 2.0 * sum(1 for key in team_games.get(t, []) if key not in mine and pid in espn.get(key, {}))
            score[pid], agree[pid] = sc, ag
        ranked = sorted(score.items(), key=lambda kv: -kv[1])
        if not ranked or ranked[0][1] < 3.0 or agree[ranked[0][0]] < 3:
            continue
        top = [pid for pid, sc in ranked if sc > ranked[0][1] - 2.0]
        if len(top) > 1:   # stesse partite e stessi minuti: decide il nome
            fit = sorted(((reg_score(names.get(uid) or "", REG["info"].get(REG["espn"].get(pid) or "", {})), pid) for pid in top), reverse=True)
            if fit[0][0] < 4.0 or fit[0][0] == fit[1][0]:
                continue
            best = fit[0][1]
        else:
            best = top[0]
        cid = REG["espn"].get(best)
        if cid is not None:
            out[uid] = cid
    return out


async def us_matches_step(d, now):
    """Tiri di ogni partita finita da Understat (xG, situazione, ultima azione prima del tiro) e pressing della partita:
    servono alle letture. Una volta per partita, quando Understat l'ha già elaborata."""
    if not LEGA["understat"]:   # coppa o campionato che Understat non copre: le letture usano i tiri della cronaca
        return
    u = load_json(us_file(season_year(d)), {}) or {}
    dates = u.get("dates") or []
    # anche le partite scaricate con una versione vecchia (senza le coordinate dei tiri)
    # (e quelle senza le formazioni di Understat, che servono a collegare i giocatori con i minuti: us_links_by_minutes)
    todo = sorted((e for e in d.get("played") or [] if e.get("status") == "finished" and e.get("hs") is not None
                   and ((MATCHES.get(str(e["id"])) or {}).get("usv") != letture.US_VERSION
                        or "usr" not in (MATCHES.get(str(e["id"])) or {}))), key=lambda e: -e["start"])
    n, left = 0, 0
    for e in todo:
        uid = us_match_id(d, e, dates)
        if not uid:
            continue
        if n >= (3 if in_window(d, now) else 12):
            left += 1
            continue
        headers = {"X-Requested-With": "XMLHttpRequest", "Referer": f"https://understat.com/match/{uid}"}
        async with HTTP["web"].get(US_MATCH.format(id=uid), headers=headers, timeout=aiohttp.ClientTimeout(total=30)) as r:
            if r.status != 200:
                raise RuntimeError(f"Understat (partita) HTTP {r.status}")
            j = json.loads(await r.text())
        x = match_entry(e)
        x.update(us=letture.parse_understat(j), usId=uid, ppda=us_ppda(d, u, e), usv=letture.US_VERSION, usr=us_rosters(j))
        n += 1
    STATUS["_usPending"] = left   # altre partite pronte su Understat: il prossimo giro arriva presto
    if n:
        VERSION["matches"] += 1
        save_json(MATCH_FILE, MATCHES)
        log(f"Tiri di Understat scaricati per {n} partite" + (f", ne mancano {left}" if left else ""))


async def opta_step(d, now):
    """Statistiche Opta della stagione da Opta Analyst (il sito di Opta): xG, xA, chance create, contrasti, intercetti,
    palloni recuperati, duelli, conduzioni progressive, gol evitati dai portieri. Ogni 6 ore."""
    # da GitHub Opta Analyst risponde 403 (blocca i computer dei centri dati): lì si usano i dati Opta del Mac, se ci sono
    if CLOUD or not LEGA.get("opta") or now - EXTRA.get("optaAt", 0) < OPTA_EVERY:
        return
    EXTRA["optaAt"] = now - OPTA_EVERY + 1800   # se va male, si riprova tra mezz'ora
    save_json(EXTRA_FILE, EXTRA)
    tmcl = fonti.parse_opta_tmcl(await web_text(fonti.OPTA_PAGE.format(lega=LEGA["opta"])))
    if not tmcl:
        raise RuntimeError("codice Opta della stagione non trovato")
    players = fonti.parse_opta_players(json.loads(await web_text(fonti.OPTA_STATS.format(tmcl=tmcl))))
    if len(players) < 200:
        raise RuntimeError(f"solo {len(players)} giocatori")
    save_json(OPTA_FILE, {"at": time.time(), "tmcl": tmcl, "players": players})
    EXTRA["optaAt"] = now
    save_json(EXTRA_FILE, EXTRA)
    log(f"Statistiche Opta (Opta Analyst): {len(players)} giocatori")
    # il sito si aggiorna su GitHub, dove Opta Analyst non risponde: i dati li porta il Mac, in un ramo a parte
    remote = (load_json(DATA_BASE / "sito.json", {}) or {}).get("remote")
    if remote:
        branch = "opta" + (f"-{LEGA['dir']}" if LEGA["dir"] else "")
        for attempt in range(3):   # GitHub a volte rifiuta un push senza motivo («failed»): si riprova
            ok, out = await asyncio.to_thread(sito.pubblica_file, remote, branch, {"opta.json": OPTA_FILE},
                                              f"Statistiche Opta della {LEGA['name']}")
            if ok:
                break
            await asyncio.sleep(20)
        log(f"Dati Opta caricati su GitHub (ramo {branch})" if ok else f"Dati Opta non caricati su GitHub: {out[-200:]}")


OPTA_POS = {"Goalkeeper": "G", "Defender": "D", "Midfielder": "M", "Forward": "F"}


def canon_opta(pid, o, team_of, words=None, mins=None):
    """Giocatore di Opta -> id dell'anagrafica (stessa squadra e stesso cognome). Omonimi nella stessa squadra (più
    giocatori con lo stesso punteggio del nome): prima vinceva il primo dell'anagrafica (Champions, Shakhtar: il gol e i
    95' del centrocampista «Pedrinho» n. 10 sul difensore omonimo n. 13, che Opta chiama «Pedro Henrique»; Liga: «Alfon
    González» del Siviglia sul portiere Fran González), ora vale chi ha il ruolo di Opta e poi i minuti ESPN più vicini,
    anche per un collegamento salvato prima. words: (squadra, parola del nome) -> id dell'anagrafica (un punteggio da
    collegamento, almeno 4, vuole una parola in comune); mins: id -> minuti ESPN della stagione."""
    cid = REG["opta"].get(pid)
    tid = team_of(o.get("team"))
    near = {c for t in tokens(o["name"]) for c in (words or {}).get((str(tid), t), ())} if tid else set()
    if len(near) > 1:
        near -= {c for k, c in REG["opta"].items() if k != pid}   # un id Opta è una persona sola
        sc = {c: reg_score(o["name"], REG["info"][c]) for c in near}
        twins = [c for c in sc if sc[c] >= 4.0 and sc[c] == max(sc.values())]
        if len(twins) > 1 and (cid is None or cid in twins):
            role, om = OPTA_POS.get(o.get("pos")), o.get("mins_played") or 0
            best = min(twins, key=lambda c: (REG["info"][c].get("pos") != role,
                                             abs((mins or {})[c] - om) if (mins or {}).get(c) is not None else math.inf))
            if cid is not None and best != cid:
                log(f"Anagrafica: Opta «{o['name']}» collegato a {REG['info'][best].get('name')} ({REG['info'][best].get('pos')}) "
                    f"e non all'omonimo ({REG['info'][cid].get('pos')})")
            cid = REG["opta"][pid] = best
    if cid is None:   # un id Opta è una persona sola: salta chi è già collegato a un altro
        owned = {c for k, c in REG["opta"].items() if k != pid}
        cid = reg_find(o["name"], [tid] if tid else None, skip=owned) or reg_find(o["name"], None, need=8.0, skip=owned)
        if cid is None:
            return None
        REG["opta"][pid] = cid
    return cid


# ---------- Champions League: forza europea, giocatori dai campionati, allenatori, proiezione della classifica ----------

ESPN_SOCCER = "https://site.api.espn.com/apis/site/v2/sports/soccer"
MONDO_DIR = CACHE / "mondo"          # calendari mensili di ESPN di campionati e coppe europee
FORZA_FILE = CACHE / "forza.json"    # attacco e difesa di tutte le squadre (europa.fit)
MONDO_EVERY = 6 * 3600
US_LEAGUES = {"eng.1": "EPL", "esp.1": "La_liga", "ita.1": "Serie_A", "ger.1": "Bundesliga", "fra.1": "Ligue_1"}
# Wikipedia in inglese: la pagina della stagione dei campionati da cui prendere gli allenatori (tabella del personale)
WIKI_LEAGUES = {"ger.1": "Bundesliga", "fra.1": "Ligue 1", "por.1": "Primeira Liga", "ned.1": "Eredivisie", "tur.1": "Süper Lig",
                "bel.1": "Belgian Pro League", "aut.1": "Austrian Football Bundesliga", "gre.1": "Super League Greece",
                "sco.1": "Scottish Premiership", "sui.1": "Swiss Super League", "den.1": "Danish Superliga",
                "nor.1": "Eliteserien", "swe.1": "Allsvenskan", "cyp.1": "Cypriot First Division", "rou.1": "Liga I",
                "rus.1": "Russian Premier League"}
CALENDAR_YEAR = {"nor.1", "swe.1"}   # stagione dentro l'anno solare: la pagina è «2026 Eliteserien»


def mondo_months(now, n=40):
    k = time.gmtime(now).tm_year * 12 + time.gmtime(now).tm_mon - 1
    return [f"{m // 12}{m % 12 + 1:02d}" for m in range(k - n + 1, k + 1)]


async def mondo_step(d, now):
    """Forza europea (solo per la Champions): calendari mensili di ESPN dei campionati delle squadre e delle coppe
    europee degli ultimi 40 mesi (i due mesi più recenti si riscaricano ogni 6 ore), poi europa.fit."""
    if not CUP or now - EXTRA.get("mondoAt", 0) < MONDO_EVERY:
        return
    EXTRA["mondoAt"] = now - MONDO_EVERY + 1800   # se va male, si riprova tra mezz'ora
    save_json(EXTRA_FILE, EXTRA)
    MONDO_DIR.mkdir(parents=True, exist_ok=True)
    months = mondo_months(now)
    todo = [(c, m) for c in europa.COMPS for m in months if m in months[-2:] or not (MONDO_DIR / f"{c}-{m}.json").exists()]
    sem = asyncio.Semaphore(6)

    async def one(c, m):
        async with sem:
            j = await espn_get(f"{ESPN_SOCCER}/{c}/scoreboard", dates=m, limit=500)
            save_json(MONDO_DIR / f"{c}-{m}.json", europa.compact(j, c))
    res = await asyncio.gather(*(one(c, m) for c, m in todo), return_exceptions=True)
    bad = [r for r in res if isinstance(r, Exception)]
    if len(bad) > len(todo) / 4:
        raise RuntimeError(f"ESPN: {len(bad)} calendari su {len(todo)} non scaricati ({errtxt(bad[0])})")
    for f in MONDO_DIR.glob("*.json"):
        if f.stem.rsplit("-", 1)[-1] not in months:
            f.unlink()
    allm = {}
    for f in MONDO_DIR.glob("*.json"):
        for m in load_json(f, []) or []:
            allm[m["id"]] = m
    done, group = europa.prepare(allm.values())
    prev = load_json(FORZA_FILE, None)
    P = await asyncio.to_thread(europa.fit, done, group, time.time(), prev, 15 if prev else 60)
    if not P:
        raise RuntimeError("forza europea: nessuna partita")
    P["at"] = time.time()
    P["matches"] = len(done)
    save_json(FORZA_FILE, P)
    VERSION["forza"] += 1
    EXTRA["mondoAt"] = now
    save_json(EXTRA_FILE, EXTRA)
    log(f"Forza europea ricalcolata: {len(done)} partite, {len(P['A'])} squadre" + (f" ({len(bad)} calendari non scaricati)" if bad else ""))


def cup_domestic_styles(d, group):
    """Stile di gioco delle squadre di Champions nel loro campionato, quando è uno di quelli dell'app (fotografia delle
    altre leghe, sola lettura): {id: {"dims", "arch", "n", "league"}}. In Champions si giocano poche partite (una o due
    a ottobre, al massimo otto nella fase campionato): lo stile misurato solo lì sarebbe quello di una o due partite."""
    out = {}
    for key, cfg in LEGHE.items():
        mine = [tid for tid in d.get("teams") or {} if group.get(tid) == cfg["espn"]]
        if cfg.get("cup") or not mine:
            continue
        base = DATA_BASE / cfg["dir"] if cfg["dir"] else DATA_BASE
        snap = load_json(base / "fotografia.json", {}) or {}
        # la Serie A ha i suoi id: la mappa ESPN -> Serie A è in cache/espn.json (come per gli allenatori)
        emap = ((load_json(base / "cache" / "espn.json", {}) or {}).get("teams") or {}) if cfg["dir"] == "" else {}
        played = {str(r["team"]): r.get("p") or 0 for r in snap.get("standings") or []}
        for tid in mine:
            lid = str(emap.get(tid, tid))
            t = (snap.get("teams") or {}).get(lid) or {}
            if t.get("dims") and played.get(lid):
                out[tid] = {"dims": t["dims"], "arch": t.get("arch"), "n": played[lid], "league": cfg["name"]}
    return out


def cup_ext(d):
    """Forza delle squadre di Champions dal modello europeo: {"mu", "he", "teams": {id: {A, D, league, n, dom}}}
    (dom: lo stile nel campionato, vedi cup_domestic_styles)."""
    P = load_json(FORZA_FILE, None)
    if not CUP or not P:
        return None
    dom = cup_domestic_styles(d, P.get("group") or {})
    teams = {tid: {"A": europa.effect(P, tid, "A"), "D": europa.effect(P, tid, "D"),
                   "league": (P.get("group") or {}).get(tid, "altro"), "n": (P.get("n") or {}).get(tid, 0),
                   "dom": dom.get(tid)}
             for tid in (d.get("teams") or {})}
    return {"mu": P["mu"], "he": P["he"], "teams": teams, "at": P.get("at")}


async def us_league_get(lg, year):
    headers = {"X-Requested-With": "XMLHttpRequest", "Referer": f"https://understat.com/league/{lg}/{year}"}
    async with HTTP["web"].get(f"https://understat.com/getLeagueData/{lg}/{year}", headers=headers,
                               timeout=aiohttp.ClientTimeout(total=40)) as r:
        if r.status != 200:
            raise RuntimeError(f"Understat {lg} HTTP {r.status}")
        return json.loads(await r.text())


# base dei giocatori di Champions: i cinque campionati di Understat e quelli con gli xG fatti dalla cronaca ESPN
# (Eredivisie e Portogallo: PSV, Feyenoord, Sporting, Porto...). In Turchia gli xG non ci sono.
CUP_SOURCES = dict(US_LEAGUES, **{"ned.1": "espn:eredivisie", "por.1": "espn:portugal"})


def cup_league_file(lg, y):
    """File della stagione y di un campionato, nel formato di Understat."""
    if lg.startswith("espn:"):
        return DATA_BASE / lg[5:] / "cache" / f"understat-{y}.json"
    return CACHE / f"understat-{lg}-{y}.json"


def cup_us_teams(d):
    """Squadra di Champions -> (campionato Understat, nome della squadra su Understat), scegliendo solo tra le squadre del
    suo campionato (così «Real Sociedad» non diventa «Real Madrid»)."""
    P = load_json(FORZA_FILE, None) or {}
    y = season_year(d)
    out = {}
    for tid, o in (d.get("teams") or {}).items():
        lg = CUP_SOURCES.get((P.get("group") or {}).get(tid))
        if not lg:
            continue
        titles = [t["title"] for t in ((load_json(cup_league_file(lg, y), {}) or {}).get("teams") or {}).values()]
        t = o["team"]
        names = [t.get("name"), t.get("fullName"), t.get("shortName")]
        sc = lambda title: max(difflib.SequenceMatcher(None, " ".join(tok_seq(title)), " ".join(tok_seq(n))).ratio()
                               for n in names if n) + .3 * len(tokens(title) & tokens(*names))
        best = max(titles, key=sc, default=None)
        if best and sc(best) >= .75:
            out[tid] = (lg, best)
    return out


CUP_BASE_KEYS = ["totalShots", "shotsOnTarget", "fouls", "wasFouled", "yellowCards", "redCards", "expectedGoals",
                 "expectedAssists", "goals", "assists", "saves", "keyPasses", "npg", "npxG", "xGChain", "xGBuildup"]


def cup_domestic_players():
    """Numeri dei giocatori nei campionati dell'app (stagione in corso e scorsa, sola lettura): {id ESPN: numeri}.
    Oltre agli xG hanno quello che viene dai tabellini ESPN: tiri in porta, falli fatti e subiti, cartellini, parate.
    Understat da solo non ha i falli: senza questa base Muriqi (Fenerbahçe, una partita di Champions con 3 falli in
    71') si prendeva quasi tutti i falli previsti della squadra e il 73% di probabilità di giallo. Una statistica che
    manca in una parte delle partite (gli xG in Turchia) si riporta a tutti i minuti con il ritmo delle altre. Con il
    ruolo, questi giocatori fanno anche le medie per ruolo della coppa (model.posavg): senza, chi aveva una sola partita
    di Champions e nessun campionato dell'app (Shakhtar, Bodø/Glimt...) aveva come falli per 90' quelli di quella
    partita, 0 o 11."""
    acc = {}
    for key, cfg in LEGHE.items():
        if cfg.get("cup"):
            continue
        base = DATA_BASE / cfg["dir"] if cfg["dir"] else DATA_BASE
        info = ((load_json(base / "cache" / "giocatori.json", {}) or {}).get("info")) or {}
        recs = ((load_json(base / "cache" / "data.json", {}) or {}).get("players") or []) \
            + ((load_json(base / "cache" / "prior.json", {}) or {}).get("players") or [])
        for r in recs:
            eid = (info.get(str(r.get("id"))) or {}).get("espnId")
            m = r.get("minutesPlayed") or 0
            if not eid or m <= 0:
                continue
            a = acc.setdefault(str(eid), {"minutesPlayed": 0.0, "_min": {}})
            if r.get("pos") and not a.get("pos"):   # serve alle medie di ruolo (prima la stagione in corso)
                a["pos"] = r["pos"]
            a["minutesPlayed"] += m
            for k in CUP_BASE_KEYS:
                if r.get(k) is not None:
                    a[k] = a.get(k, 0) + r[k]
                    a["_min"][k] = a["_min"].get(k, 0) + m
    for a in acc.values():
        mins = a.pop("_min")
        for k, km in mins.items():
            if km and km < a["minutesPlayed"]:
                a[k] = a[k] * a["minutesPlayed"] / km
    return acc


def cup_prior_players(d):
    """Base dei giocatori di Champions: le loro statistiche nel loro campionato (stagione in corso e scorsa): i cinque
    di Understat, più Eredivisie e Portogallo con gli xG fatti dalla cronaca ESPN (CUP_SOURCES). In Champions si giocano
    al massimo 8 partite: senza questa base i numeri per 90' sarebbero solo medie di ruolo."""
    y = season_year(d)
    teams = cup_us_teams(d)
    by_title = {(lg, title): tid for tid, (lg, title) in teams.items()}
    usmap = REG.setdefault("usd", {})
    # collegamenti già fatti dalle altre leghe dell'app (Understat -> giocatore -> id ESPN): gli id ESPN sono gli stessi
    # in campionato e in Champions, quindi il collegamento è esatto (niente nomi da confrontare)
    dom = {}
    for key, cfg in LEGHE.items():
        if not cfg.get("cup") and cfg.get("understat"):
            reg = load_json((DATA_BASE / cfg["dir"] if cfg["dir"] else DATA_BASE) / "cache" / "giocatori.json", {}) or {}
            for us_id, c in (reg.get("us") or {}).items():
                eid = ((reg.get("info") or {}).get(str(c)) or {}).get("espnId")
                if eid:
                    dom[str(us_id)] = str(eid)
    out = {}
    for yy in (y, y - 1):
        for lg in sorted(set(CUP_SOURCES.values())):
            f = cup_league_file(lg, yy)
            for u in ((statistiche.understat_parse(load_json(f, {})) or {}).get("players") or []) if f.exists() else []:
                if lg.startswith("espn:"):   # id di ESPN, da non confondere con quelli di Understat
                    u["usId"] = "e" + u["usId"]
                # id ESPN (Eredivisie, Portogallo) o Understat già collegato da una lega dell'app: collegamento esatto,
                # e se quel giocatore non è in Champions non si cerca un omonimo (Pablo García del Racing non è Fran
                # García del Betis)
                eid = u["usId"][1:] if u["usId"].startswith("e") else dom.get(u["usId"])
                if eid:
                    cid = REG["espn"].get(eid)
                    if cid is None:
                        usmap.pop(u["usId"], None)
                    elif usmap.get(u["usId"]) != cid:
                        usmap[u["usId"]] = cid
                cid = usmap.get(u["usId"])
                if cid is not None and role_clash(cid, u.get("usPos")):
                    usmap.pop(u["usId"], None)
                    cid = None
                if cid is None and not eid and yy == y:   # il collegamento si fa con la stagione in corso, per squadra
                    tids = [by_title.get((lg, t.strip())) for t in (u.get("team") or "").split(",")]
                    tids = [t for t in tids if t]
                    fam = u["usId"].startswith("e")   # un id per persona in ogni fonte (Understat, ESPN)
                    owned = {c for k, c in usmap.items() if k != u["usId"] and k.startswith("e") == fam}
                    cid = reg_find(u["name"], tids, skip=owned) if tids else None
                    if cid and role_clash(cid, u.get("usPos")):
                        cid = None
                    if cid:
                        usmap[u["usId"]] = cid
                if cid is None:
                    continue
                p = out.setdefault(cid, {"id": int(cid), "minutesPlayed": 0.0})
                for k in US_FIELDS:
                    if u.get(k) is not None:
                        p[k] = p.get(k, 0) + u[k]
    # chi gioca in un campionato dell'app ha come base i suoi numeri completi lì (anche falli e cartellini)
    for eid, a in cup_domestic_players().items():
        cid = REG["espn"].get(eid)
        if cid is not None:
            out[cid] = dict(a, id=int(cid))
    return list(out.values())


def uefa_coaches(d):
    """Allenatori ufficiali della UEFA: chi era in panchina nell'ultima partita di Champions di ogni squadra."""
    out = {}
    for e in sorted(d.get("played") or [], key=lambda e: e["start"]):
        coach = (((MATCHES.get(str(e["id"])) or {}).get("uefa") or {}).get("coach") or {})
        for side in ("home", "away"):
            if coach.get(side):
                out[str(e[side]["id"])] = coach[side]
    return out


async def cup_coaches(d, now):
    """Allenatori delle squadre di Champions: quello ufficiale della UEFA (formazioni dell'ultima partita); per chi non
    ha ancora giocato, dalle altre leghe dell'app (Serie A, Premier, Liga) e, per gli altri campionati, dalla tabella
    del personale della loro pagina su Wikipedia in inglese (una volta al giorno)."""
    if not CUP:
        return
    official = uefa_coaches(d)
    if official and any((COACHES.get(t, {}).get("manager") or {}).get("name") != n for t, n in official.items()):
        for tid, name in official.items():
            COACHES.setdefault(tid, {})["manager"] = {"id": None, "name": name}
            COACHES[tid]["wiki"] = {"name": name, "new": None, "left": None}
            COACHES[tid]["src"] = "UEFA"
        save_json(COACH_FILE, COACHES)
        VERSION["coaches"] += 1
        log(f"Allenatori ufficiali UEFA: {len(official)} squadre")
    if now - EXTRA.get("coachAt", 0) < 86400 or len(official) >= len(d.get("teams") or {}):
        return
    EXTRA["coachAt"] = now - 86400 + 3600
    P = load_json(FORZA_FILE, None) or {}
    group = P.get("group") or {}
    found = {}
    # le altre leghe dell'app: Premier e Liga hanno gli id ESPN; la Serie A li traduce con la sua mappa
    for key, cfg in LEGHE.items():
        if cfg.get("cup"):
            continue
        base = DATA_BASE / cfg["dir"] if cfg["dir"] else DATA_BASE
        co = load_json(base / "cache" / "coaches.json", {}) or {}
        emap = (load_json(base / "cache" / "espn.json", {}) or {}).get("teams") or {}
        for tid in d.get("teams") or {}:
            c = co.get(emap.get(tid, tid)) if cfg["dir"] == "" else co.get(tid)
            name = ((c or {}).get("manager") or {}).get("name")
            if name:
                found[tid] = name
    y = season_year(d)
    for comp, title in WIKI_LEAGUES.items():
        mine = [tid for tid in d.get("teams") or {} if group.get(tid) == comp and tid not in found]
        if not mine:
            continue
        page = f"{time.gmtime(now).tm_year} {title}" if comp in CALENDAR_YEAR else f"{y}–{(y + 1) % 100:02d} {title}"
        try:
            base = {"action": "parse", "page": page, "format": "json", "formatversion": "2"}
            get = lambda **p: web_text(fonti.WIKI_EN + "?" + urlencode(dict(base, **p)), headers={"User-Agent": WIKI_UA})
            secs = json.loads(await get(prop="sections")).get("parse", {}).get("sections") or []
            sec = next((x["index"] for x in secs if "personnel" in x["line"].lower()), None)
            table = fonti.parse_personale_en(json.loads(await get(prop="text", section=sec))["parse"]["text"]) if sec else {}
            # senza tabella del personale (es. Belgio 2026/27): per ogni squadra l'ultimo allenatore arrivato nei cambi
            # della stagione (la tabella è in ordine di data, quindi l'ultimo vince); chi non ha cambiato resta senza
            chg = next((x["index"] for x in secs if "managerial" in x["line"].lower()), None)
            if not table and chg:
                for c in fonti.parse_cambi_en(json.loads(await get(prop="text", section=chg))["parse"]["text"]):
                    if c.get("in") and c.get("team"):
                        table[c["team"]] = [{"name": c["in"]}]
        except Exception as e:
            log(f"Allenatori ({page}) non letti: {errtxt(e)}")
            continue
        for tid in mine:
            t = d["teams"][tid]["team"]
            tk = tokens(t.get("name"), t.get("fullName"), t.get("shortName"))
            best = max(table, key=lambda k: len(tokens(k) & tk), default=None)
            if best and len(tokens(best) & tk) >= max(1, min(2, len(tokens(best)))) and table[best]:
                found[tid] = table[best][-1]["name"]
    n = 0
    for tid, name in found.items():
        if tid in official:   # la UEFA vale più delle altre fonti
            continue
        c = COACHES.setdefault(tid, {})
        if ((c.get("manager") or {}).get("name")) != name:
            n += 1
        c["manager"] = {"id": None, "name": name}
        c["wiki"] = {"name": name, "new": None, "left": None}
    if n:
        save_json(COACH_FILE, COACHES)
        VERSION["coaches"] += 1
    EXTRA["coachAt"] = now
    save_json(EXTRA_FILE, EXTRA)
    log(f"Allenatori della Champions: {len(official)} dalla UEFA, {len([t for t in found if t not in official])} da altre fonti, "
        f"su {len(d.get('teams') or {})} squadre")


# Champions: i dati ufficiali della UEFA (gli stessi di uefa.com): statistiche di squadra con quelle del tracciamento
# (km percorsi, sprint, velocità massima), statistiche di ogni giocatore, formazioni con gli allenatori e il migliore in
# campo. Nessuna chiave: sono le richieste pubbliche del sito della UEFA.
UEFA_MATCHES = "https://match.uefa.com/v5/matches"
UEFA_STATS = "https://matchstats.uefa.com/v2"
UEFA_FILE = CACHE / "uefa.json"   # partite UEFA della stagione e collegamento con quelle di ESPN
UEFA_VERSION = 1
# statistica UEFA -> chiave corta (squadra)
UEFA_TEAM = {"ball_possession": "poss", "attempts": "sh", "attempts_on_target": "sot", "passes_attempted": "pa",
             "passes_completed": "pc", "passes_long_attempted": "pl", "cross_attempted": "cr", "corners": "cor",
             "recovered_ball": "rec", "recovered_balls_opposite": "reco", "tackles": "tk", "tackles_won": "tkw",
             "distance_covered": "km", "distance_covered_in_possession": "kmp", "distance_covered_not_in_possession": "kmn",
             "sprints": "spr", "top_speed": "vmax", "distance_covered_in_high_intensity_running": "hi",
             "ball_touches_by_player_penalty_area": "box", "delivery_into_penalty_area": "dlv", "dribbling": "drb",
             "dribbling_successful": "drbw", "fouls_committed": "fc", "saves": "sv", "offsides": "off"}
# statistica UEFA -> chiave corta (giocatore)
UEFA_PLAYER = {"minutes_played_official": "min", "distance_covered": "km", "top_speed": "vmax", "sprints": "spr",
               "distance_covered_in_high_intensity_running": "hi", "recovered_ball": "rec", "recovered_balls_opposite": "reco",
               "tackles_won": "tkw", "passes_attempted": "pa", "passes_completed": "pc", "key_passes": "kp",
               "total_ball_touches": "tch", "dribbling_successful": "drbw", "attempts": "sh", "attempts_on_target": "sot",
               "goals": "g", "assists": "a", "fouls_committed": "fc", "fouls_suffered": "fs", "saves": "sv"}


async def uefa_get(url, **params):
    async with HTTP["web"].get(url, params=params or None, timeout=aiohttp.ClientTimeout(total=60)) as r:
        if r.status != 200:
            raise RuntimeError(f"UEFA HTTP {r.status}")
        return await r.json(content_type=None)


def _uefa_name(x):
    return ((x.get("translations") or {}).get("name") or {}).get("EN") or x.get("internationalName") or x.get("name")


def _uefa_stats(rows, keys):
    out = {}
    for x in rows or []:
        k = keys.get(x.get("name"))
        if k:
            try:
                out[k] = round(float(x.get("value")), 3)
            except (TypeError, ValueError):
                pass
    return out


def uefa_link(d, U):
    """Partita ESPN -> partita UEFA: stessa ora (entro 3 ore) e nomi delle squadre più simili."""
    def sc(espn_team, name):
        a, b = " ".join(tok_seq(espn_team.get("fullName") or espn_team["name"])), " ".join(tok_seq(name))
        c = " ".join(tok_seq(espn_team["name"]))
        return max(difflib.SequenceMatcher(None, a, b).ratio(), difflib.SequenceMatcher(None, c, b).ratio()) + \
            .3 * len(tokens(espn_team["name"], espn_team.get("fullName")) & tokens(name))
    link = {}
    for e in (x for lst in ("played", "live", "next") for x in d.get(lst) or []):
        best, bs = None, 0.0
        for uid, m in (U.get("matches") or {}).items():
            if abs((m.get("t") or 0) - e["start"]) > 3 * 3600:
                continue
            v = sc(e["home"], m["h"][1]) + sc(e["away"], m["a"][1])
            if v > bs:
                best, bs = uid, v
        if best and bs >= 1.0:
            link[str(e["id"])] = best
    return link


async def uefa_step(d, now):
    """Dati ufficiali della UEFA delle partite giocate (al massimo 12 per giro: ogni partita sono tre richieste)."""
    if not CUP:
        return
    U = load_json(UEFA_FILE, {}) or {}
    year = season_year(d) + 1   # per la UEFA la stagione 2026/27 è il 2027
    played = [e for e in d.get("played") or [] if e.get("hs") is not None and e.get("status") == "finished"]
    todo = [e for e in played if ((MATCHES.get(str(e["id"])) or {}).get("uefa") or {}).get("v") != UEFA_VERSION]
    unlinked = [e for e in todo if str(e["id"]) not in (U.get("link") or {})]
    no_ref = not any("ref" in m for m in (U.get("matches") or {}).values())   # elenco salvato prima degli arbitri
    if U.get("year") != year or now - U.get("at", 0) > 6 * 3600 or (unlinked and now - U.get("at", 0) > 1800) or no_ref:
        ms = []
        for off in range(0, 500, 100):
            j = await uefa_get(UEFA_MATCHES, competitionId=1, seasonYear=year, limit=100, offset=off, order="ASC")
            ms += j or []
            if len(j or []) < 100:
                break
        mm = {}
        for m in ms:
            try:
                t = espn_time((m.get("kickOffTime") or {}).get("dateTime"))
            except (TypeError, ValueError, AttributeError):
                continue
            potm = ((m.get("playerOfTheMatch") or {}).get("player") or {})
            refs = [r for r in m.get("referees") or [] if r.get("role") == "REFEREE"]
            mm[str(m["id"])] = {"t": t, "h": [str(m["homeTeam"]["id"]), _uefa_name(m["homeTeam"])],
                                "a": [str(m["awayTeam"]["id"]), _uefa_name(m["awayTeam"])], "st": m.get("status"),
                                "potm": [str(potm["id"]), _uefa_name(potm)] if potm.get("id") else None,
                                "ref": _uefa_name(refs[0].get("person") or {}) if refs else None}
        U = {"year": year, "at": now, "matches": mm}
        U["link"] = uefa_link(d, U)
        save_json(UEFA_FILE, U)
    # arbitro designato dalla UEFA: in Champions ESPN non lo dà prima della partita (e dopo solo per metà delle
    # partite), la UEFA lo pubblica due o tre giorni prima. Nelle partite giocate vale quello di ESPN se c'è
    finished = {str(e["id"]) for e in played}
    refs = 0
    for eid, uid in (U.get("link") or {}).items():
        ref = ((U.get("matches") or {}).get(uid) or {}).get("ref")
        cur = ((MATCHES.get(eid) or {}).get("referee") or {}).get("name")
        if not ref or (cur and (same_ref(cur, ref) or eid in finished)):
            continue
        MATCHES.setdefault(eid, {})["referee"] = {"name": ref, "src": "UEFA"}
        refs += 1
    if refs:
        save_json(MATCH_FILE, MATCHES)
        VERSION["matches"] += 1
        log(f"Arbitri dalla UEFA: {refs} partite")
    n = 0
    for e in todo:
        uid = (U.get("link") or {}).get(str(e["id"]))
        m = (U.get("matches") or {}).get(uid or "")
        if not m or m.get("st") != "FINISHED" or n >= 12:
            continue
        ts = await uefa_get(f"{UEFA_STATS}/team-statistics/{uid}")
        ps = await uefa_get(f"{UEFA_STATS}/player-statistics/{uid}")
        lu = await uefa_get(f"{UEFA_MATCHES}/{uid}/lineups")
        side_of = {m["h"][0]: "home", m["a"][0]: "away"}
        t = {side_of[str(x.get("teamId"))]: _uefa_stats(x.get("statistics"), UEFA_TEAM) for x in ts or [] if str(x.get("teamId")) in side_of}
        people, coach = {}, {}
        for side, key in (("home", "homeTeam"), ("away", "awayTeam")):
            T_ = (lu or {}).get(key) or {}
            for x in (T_.get("field") or []) + (T_.get("bench") or []):
                pl = x.get("player") or {}
                if pl.get("id"):
                    people[str(pl["id"])] = (side, _uefa_name(pl), x.get("jerseyNumber"), pl.get("fieldPosition"))
            c = ((T_.get("coaches") or [{}])[0] or {}).get("person") or {}
            if _uefa_name(c):
                coach[side] = _uefa_name(c)
        pls = {"home": [], "away": []}
        for x in ps or []:
            pid = str(x.get("playerId"))
            st = _uefa_stats(x.get("statistics"), UEFA_PLAYER)
            side, name, no, pos = people.get(pid) or (side_of.get(str(x.get("teamId"))), None, None, None)
            if side and name and st.get("min"):
                pls[side].append(dict(st, id=pid, n=name, no=no, pos=pos))
        if not t.get("home") or not t.get("away"):
            continue   # la UEFA non ha ancora le statistiche: si riprova al prossimo giro
        x = MATCHES.setdefault(str(e["id"]), {})
        x["uefa"] = {"v": UEFA_VERSION, "id": uid, "t": t, "p": pls, "coach": coach, "potm": m.get("potm")}
        n += 1
    if n:
        save_json(MATCH_FILE, MATCHES)
        VERSION["matches"] += 1
        log(f"Dati UEFA: {n} partite")


def uefa_teams(d):
    """Medie a partita delle statistiche UEFA di ogni squadra in questa Champions e posizione tra le squadre
    (1 = il valore più alto). -> {id: {"n": partite, "avg": {chiave: media}, "rk": {chiave: posizione}, "N": squadre}}."""
    sums = {}
    for e in d.get("played") or []:
        u = (MATCHES.get(str(e["id"])) or {}).get("uefa") or {}
        for side in ("home", "away"):
            st = (u.get("t") or {}).get(side)
            if not st:
                continue
            o = sums.setdefault(str(e[side]["id"]), {"n": 0, "s": {}, "against": {}})
            o["n"] += 1
            for k, v in st.items():
                o["s"][k] = o["s"].get(k, 0.0) + v
            for k, v in ((u.get("t") or {}).get("away" if side == "home" else "home") or {}).items():
                o["against"][k] = o["against"].get(k, 0.0) + v
    out = {}
    for tid, o in sums.items():
        avg = {k: v / o["n"] for k, v in o["s"].items()}
        a = o["s"]
        if a.get("pa"):
            avg["pacc"] = 100 * a.get("pc", 0) / a["pa"]           # precisione dei passaggi
            avg["plong"] = 100 * a.get("pl", 0) / a["pa"]          # quota di lanci lunghi
        if a.get("rec"):
            avg["recohi"] = 100 * a.get("reco", 0) / a["rec"]      # palloni recuperati nella metà campo avversaria, in %
        if a.get("km"):
            avg["kmnp"] = 100 * a.get("kmn", 0) / a["km"]          # quota di corsa senza palla
        avg["shc"] = o["against"].get("sh", 0) / o["n"]            # tiri concessi
        out[tid] = {"n": o["n"], "avg": {k: round(v, 2) for k, v in avg.items()}}
    keys = {k for o in out.values() for k in o["avg"]}
    for k in keys:
        vals = sorted((o["avg"][k] for o in out.values() if k in o["avg"]), reverse=True)
        for o in out.values():
            if k in o["avg"]:
                o.setdefault("rk", {})[k] = vals.index(o["avg"][k]) + 1
    for o in out.values():
        o["N"] = len(out)
    return out


def uefa_players(d):
    """Statistiche UEFA dei giocatori in questa Champions, sommate e collegate all'anagrafica (squadra, nome, numero).
    -> {id del giocatore: {"n": partite, "min", "km", "vmax" (la più alta), "spr", "hi", "rec", "reco", "tkw", "pa", "pc",
    "kp", "tch", "drbw"}}."""
    out = {}
    for e in d.get("played") or []:
        u = (MATCHES.get(str(e["id"])) or {}).get("uefa") or {}
        for side in ("home", "away"):
            tid = str(e[side]["id"])
            for x in (u.get("p") or {}).get(side) or []:
                cid = UEFA_PLAYER_IDS.get(x["id"])
                if cid is None:
                    cid = reg_find(x["n"], [tid], x.get("no"))
                    UEFA_PLAYER_IDS[x["id"]] = cid
                if not cid:
                    continue
                o = out.setdefault(cid, {"n": 0})
                o["n"] += 1
                for k, v in x.items():
                    if k in ("id", "n", "no", "pos"):
                        continue
                    o[k] = max(o.get(k, 0), v) if k == "vmax" else round(o.get(k, 0) + v, 3)
    return out
UEFA_PLAYER_IDS = {}   # id UEFA -> id dell'anagrafica (si ricalcola a ogni avvio)


def uefa_out(d):
    """Dati UEFA per le pagine: {"uefaTeams": uefa_teams, "uefaPlayers": {id: totali}} (vuoti se non ci sono)."""
    try:
        return {"uefaTeams": _r(uefa_teams(d), 2), "uefaPlayers": _r(uefa_players(d), 2)}
    except Exception as ex:
        log(f"Dati UEFA per le pagine non preparati: {errtxt(ex)}")
        return {}


def cup_projection(d, A, sims=5000):
    """Champions simulata `sims` volte con i gol attesi del modello: fase campionato (le partite che mancano; criteri:
    punti, differenza reti, gol fatti, gol fatti in trasferta, vittorie, vittorie in trasferta, poi a sorte) e poi
    l'eliminazione diretta del formato dal 2024/25. Spareggi: 9ª/10ª contro 23ª/24ª, 11ª/12ª contro 21ª/22ª, 13ª/14ª
    contro 19ª/20ª, 15ª/16ª contro 17ª/18ª. Ottavi: le vincenti degli spareggi delle coppie 15/16, 13/14, 11/12 e 9/10
    contro 1ª/2ª, 3ª/4ª, 5ª/6ª e 7ª/8ª. Tabellone: in ogni metà un quarto tra le vie di 1ª/2ª e 7ª/8ª e uno tra 3ª/4ª e
    5ª/6ª, poi la semifinale tra i due; 1ª e 2ª (come 3ª e 4ª...) stanno in metà diverse. Chi è più in alto in classifica
    gioca il ritorno in casa negli spareggi e negli ottavi; nei quarti e in semifinale lo decide il sorteggio. Andata e
    ritorno, poi supplementari (un terzo dei gol attesi) e rigori a sorte; finale in campo neutro. I turni già
    sorteggiati o giocati (partite di ESPN) si usano come sono, con i risultati veri; quello che il sorteggio non ha
    ancora deciso si sorteggia a ogni simulazione.
    -> {id: {"top8", "po", "out", "pts", "r16", "qf", "sf", "final", "win"}, "_left": partite della fase campionato
    che mancano, "_n": squadre, "_ko": turno a cui è arrivata l'eliminazione diretta}."""
    evs = {str(e["id"]): e for lst in ("played", "live", "next") for e in d.get(lst) or []}.values()
    league = [e for e in evs if e.get("stage") in (None, "league-phase")]
    teams = list(A["T"])
    # serve il calendario intero della fase campionato (8 partite per squadra): con partite mancanti sarebbe sbagliata
    if len(league) < len(teams) * 8 // 2 or len(teams) < 36:
        return None
    done_ = lambda e: e.get("status") == "finished" and e.get("hs") is not None
    rest = [e for e in league if not done_(e)]
    base = {tid: [0, 0, 0, 0, 0, 0] for tid in teams}   # punti, differenza, gol, gol fuori, vittorie, vittorie fuori

    def add(st, h, a, gh, ga):
        sh, sa = st[h], st[a]
        sh[1] += gh - ga; sa[1] += ga - gh; sh[2] += gh; sa[2] += ga; sa[3] += ga
        if gh > ga:
            sh[0] += 3; sh[4] += 1
        elif ga > gh:
            sa[0] += 3; sa[4] += 1; sa[5] += 1
        else:
            sh[0] += 1; sa[0] += 1
    for e in league:
        h, a = str(e["home"]["id"]), str(e["away"]["id"])
        if done_(e) and h in base and a in base:
            add(base, h, a, e["hs"], e["as"])
    lam_cache = {}

    def lam(h, a, neutral=False):
        k = (h, a, neutral)
        if k not in lam_cache:
            lam_cache[k] = model.base_lambdas(A, h, a, neutral)
        return lam_cache[k]
    rest_l = [(str(e["home"]["id"]), str(e["away"]["id"])) for e in rest if str(e["home"]["id"]) in base and str(e["away"]["id"]) in base]
    # classifica vera a fase campionato finita (ESPN ha anche gli ultimi criteri, come i punti delle avversarie)
    table = (d.get("standings") or {}).get("total") or []
    real_order = [str(r["team"]["id"]) for r in sorted(table, key=lambda r: r["pos"] or 99)] if not rest else None
    if real_order and set(real_order) != set(teams):
        real_order = None
    # eliminazione diretta già sorteggiata: {fase: {coppia: [andata, ritorno]}}
    ko = {}
    for e in evs:
        if e.get("stage") in KO_STAGES:
            pair = frozenset((str(e["home"]["id"]), str(e["away"]["id"])))
            ko.setdefault(e["stage"], {}).setdefault(pair, []).append(e)
    ko_need = {"knockout-round-playoffs": 8, "round-of-16": 8, "quarterfinals": 4, "semifinals": 2, "final": 1}
    ko = {st: v for st, v in ko.items() if len(v) == ko_need[st]}   # un turno conta solo se è sorteggiato tutto
    rng = random.Random(7)

    def pois(l):
        k, p, lim = 0, 1.0, math.exp(-l)
        while True:
            p *= rng.random()
            if p <= lim:
                return k
            k += 1

    def tie(a, b, real=None, final=False):
        """Vincente tra a e b; a gioca l'andata in casa, b il ritorno. real: partite vere di ESPN della coppia."""
        real = sorted(real or [], key=lambda e: e["start"])
        if final:
            e = real[0] if real else None
            if e and done_(e) and e.get("adv"):
                return str(e[e["adv"]]["id"])
            lh, la = lam(a, b, True)
            ga, gb = pois(lh), pois(la)
            if ga == gb:
                ga += pois(lh / 3); gb += pois(la / 3)
            return a if ga > gb else b if gb > ga else rng.choice((a, b))
        if real:
            a = str(real[0]["home"]["id"])
            b = str(real[0]["away"]["id"])
            if len(real) > 1 and done_(real[1]) and real[1].get("adv"):
                return str(real[1][real[1]["adv"]]["id"])
        tot = {a: 0, b: 0}
        for leg, (h, w) in enumerate(((a, b), (b, a))):
            e = real[leg] if real and leg < len(real) else None
            if e and done_(e):
                tot[str(e["home"]["id"])] += e["hs"]; tot[str(e["away"]["id"])] += e["as"]
            else:
                lh, la = lam(h, w)
                tot[h] += pois(lh); tot[w] += pois(la)
        if tot[a] == tot[b]:   # supplementari nel ritorno (in casa di b), poi rigori
            lh, la = lam(b, a)
            tot[b] += pois(lh / 3); tot[a] += pois(la / 3)
        return a if tot[a] > tot[b] else b if tot[b] > tot[a] else rng.choice((a, b))

    def two_leg(seeded, other, stage):
        """Coppia degli spareggi o degli ottavi: ritorno in casa della testa di serie, o le partite vere."""
        real = ko.get(stage, {}).get(frozenset((seeded, other)))
        return tie(other, seeded, real)

    keys = ("top8", "po", "out", "r16", "qf", "sf", "final", "win")
    count = {t: dict.fromkeys(keys, 0) for t in teams}
    pts = dict.fromkeys(teams, 0.0)
    for _ in range(sims):
        if real_order:
            order = real_order
            for t in teams:
                pts[t] += base[t][0]
        else:
            st = {t: list(v) for t, v in base.items()}
            for h, a in rest_l:
                lh, la = lam(h, a)
                add(st, h, a, pois(lh), pois(la))
            order = sorted(st, key=lambda t: (st[t][0], st[t][1], st[t][2], st[t][3], st[t][4], st[t][5], rng.random()), reverse=True)
            for t in teams:
                pts[t] += st[t][0]
        rank = {t: i + 1 for i, t in enumerate(order)}
        for i, t in enumerate(order):
            count[t]["top8" if i < 8 else "po" if i < 24 else "out"] += 1
        # spareggi: per ogni coppia di teste di serie (9/10, 11/12, 13/14, 15/16) le due avversarie (23/24, 21/22...)
        po_win = {}   # indice della coppia (0: 9/10 ... 3: 15/16) -> [vincenti]
        if "knockout-round-playoffs" in ko:
            for pair, legs in ko["knockout-round-playoffs"].items():
                x, y = sorted(pair, key=lambda t: rank[t])
                w = tie(y, x, legs)
                po_win.setdefault(min(3, max(0, (rank[x] - 9) // 2)), []).append(w)
        else:
            for k in range(4):
                seeds, others = order[8 + 2 * k:10 + 2 * k], order[22 - 2 * k:24 - 2 * k]
                if rng.random() < .5:
                    others = others[::-1]
                po_win[k] = [two_leg(s_, o_, "knockout-round-playoffs") for s_, o_ in zip(seeds, others)]
        # ottavi: ogni squadra prende il «seme» della testa di serie del suo ottavo (1-8)
        r16_win = {}   # seme -> vincente
        if "round-of-16" in ko:
            for pair, legs in ko["round-of-16"].items():
                x, y = sorted(pair, key=lambda t: rank[t])
                r16_win[min(rank[x], 8)] = tie(y, x, legs)
                for t in pair:
                    count[t]["r16"] += 1
        else:
            for k, (s1, s2) in enumerate(((7, 8), (5, 6), (3, 4), (1, 2))):
                ws = list(po_win.get(k, []))
                rng.shuffle(ws)
                for seed, w in zip((s1, s2), ws):
                    top = order[seed - 1]
                    count[top]["r16"] += 1
                    count[w]["r16"] += 1
                    r16_win[seed] = two_leg(top, w, "round-of-16")
        # metà del tabellone: per ogni coppia di semi (1/2, 3/4, 5/6, 7/8) uno per metà, a sorte
        half = {}
        for s1, s2 in ((1, 2), (3, 4), (5, 6), (7, 8)):
            hs_ = (0, 1) if rng.random() < .5 else (1, 0)
            half[s1], half[s2] = hs_
        seed_of = {w: sd for sd, w in r16_win.items()}
        for w in r16_win.values():
            count[w]["qf"] += 1
        if "quarterfinals" in ko:
            qf = [(pair, legs) for pair, legs in ko["quarterfinals"].items()]
            qf_w = []
            for pair, legs in qf:
                x, y = sorted(pair)
                qf_w.append((tie(x, y, legs), min(seed_of.get(t, 9) for t in pair)))
        else:
            qf_w = []
            for h_ in (0, 1):
                for g1, g2 in (((1, 2), (7, 8)), ((3, 4), (5, 6))):
                    a_ = next(r16_win[sd] for sd in g1 if half[sd] == h_)
                    b_ = next(r16_win[sd] for sd in g2 if half[sd] == h_)
                    if rng.random() < .5:
                        a_, b_ = b_, a_
                    qf_w.append((tie(a_, b_), min(seed_of[a_], seed_of[b_])))
        for w, _ in qf_w:
            count[w]["sf"] += 1
        if "semifinals" in ko:
            sf_w = [tie(*sorted(pair), legs) for pair, legs in ko["semifinals"].items()]
        else:
            # in ogni semifinale un quarto della via 1/2-7/8 e uno della via 3/4-5/6
            g12 = [w for w, sd in qf_w if sd in (1, 2, 7, 8)]
            g34 = [w for w, sd in qf_w if sd not in (1, 2, 7, 8)]
            if len(g12) != 2 or len(g34) != 2:   # quarti veri che non seguono lo schema: semifinali a sorte
                ws = [w for w, _ in qf_w]
                rng.shuffle(ws)
                g12, g34 = ws[:2], ws[2:]
            elif "quarterfinals" not in ko:
                g34 = [next(w for w, sd in qf_w if sd not in (1, 2, 7, 8) and half[sd] == half[seed_of[x]]) for x in g12]
            else:
                rng.shuffle(g34)
            sf_w = []
            for a_, b_ in zip(g12, g34):
                if rng.random() < .5:
                    a_, b_ = b_, a_
                sf_w.append(tie(a_, b_))
        for w in sf_w:
            count[w]["final"] += 1
        fin = ko.get("final")
        a_, b_ = sf_w
        count[tie(a_, b_, next(iter(fin.values())) if fin else None, final=True)]["win"] += 1
    stage = next((st for st in reversed(KO_STAGES) if st in ko), None)
    return {t: {k: round(c[k] / sims, 3) for k in keys} | {"pts": round(pts[t] / sims, 1)} for t, c in count.items()} | {
        "_left": len(rest_l), "_n": len(teams), "_ko": stage}


async def sources_step(d, now):
    """Understat (xG, xA, pressing, minuti) e Fantacalcio.it (media voto): ogni 6 ore e dopo le partite."""
    if ESPN_XG:   # i dati «Understat» li fa rebuild_stats con le partite ESPN
        return False
    last_end = max((e["start"] + 2.25 * 3600 for e in d.get("played") or []), default=0)
    at = EXTRA.get("usAt", 0)
    if now - at < US_EVERY and not (at < last_end + 3600 <= now):
        return False
    EXTRA["usAt"] = now - US_EVERY + 1800   # se va male, si riprova tra mezz'ora
    save_json(EXTRA_FILE, EXTRA)
    y = season_year(d)
    if CUP:   # Understat non ha la Champions: i campionati dei giocatori, per la loro base
        for lg in sorted(set(US_LEAGUES.values())):
            save_json(CACHE / f"understat-{lg}-{y}.json", await us_league_get(lg, y))
            if not (CACHE / f"understat-{lg}-{y - 1}.json").exists():
                save_json(CACHE / f"understat-{lg}-{y - 1}.json", await us_league_get(lg, y - 1))
    else:
        save_json(us_file(y), await us_get(y))
        if not us_file(y - 1).exists():
            save_json(us_file(y - 1), await us_get(y - 1))
    STATUS["usAt"] = time.time()
    if LEGA["fantacalcio"]:
        try:
            rows = statistiche.parse_fc_stats(await web_text(statistiche.FC_STATS))
            if rows:
                save_json(FC_STATS_FILE, {"at": time.time(), "players": rows})
                STATUS["fcStatsAt"] = time.time()
        except Exception as e:
            log(f"Errore Fantacalcio.it (statistiche): {errtxt(e)}")
    EXTRA["usAt"] = now
    save_json(EXTRA_FILE, EXTRA)
    log("Statistiche aggiornate da Understat" + (" e Fantacalcio.it" if LEGA["fantacalcio"] else ""))
    return True


async def espn_rosters(d, now):
    """Rose delle squadre da ESPN, una volta a settimana: servono per riconoscere i giocatori nuovi."""
    if now - EXTRA.get("rosterAt", 0) < ROSTER_EVERY:
        return
    EXTRA["rosterAt"] = now
    rev = {str(v): k for k, v in (ESPNMAP.get("teams") or {}).items()}
    n = 0
    for tid in (d.get("teams") or {}):
        if tid not in rev:
            continue
        j = await espn_get(ESPN_SITE + f"/teams/{rev[tid]}/roster")
        for a in j.get("athletes") or []:
            canon_espn(a.get("id"), a.get("displayName"), tid, a.get("jersey"),
                       ((a.get("position") or {}).get("abbreviation") or "").upper())
            n += 1
    save_json(REG_FILE, REG)
    save_json(EXTRA_FILE, EXTRA)
    refresh_squads(d)
    log(f"Rose aggiornate da ESPN: {n} giocatori")


def refresh_squads(d):
    """Rose correnti dall'anagrafica (servono a riconoscere i giocatori delle formazioni e del fantacalcio)."""
    global SQUADS
    teams = set(d.get("teams") or {})
    SQUADS = {"players": {cid: {"name": x.get("name"), "teamId": int(x["teamId"]), "pos": x.get("pos"), "num": x.get("num")}
                          for cid, x in REG["info"].items() if x.get("teamId") in teams}}
    VERSION["squads"] += 1


def reg_seed(d):
    """Primo avvio: i giocatori già noti (con i loro id) diventano la base dell'anagrafica."""
    if REG["info"]:
        return
    for p in d.get("players") or []:
        REG["info"][str(p["id"])] = {"name": p.get("name"), "teamId": str(p.get("teamId")), "pos": p.get("pos"),
                                     "num": p.get("shirtNumber") or p.get("num")}
    for pid, x in (SQUADS.get("players") or {}).items():
        REG["info"].setdefault(str(pid), {"name": x.get("name"), "teamId": str(x.get("teamId")), "pos": x.get("pos"),
                                          "num": x.get("num")})
    save_json(REG_FILE, REG)


def repair_registry(d):
    """Separa i giocatori che l'anagrafica aveva unito per errore quando bastava il nome di battesimo (es. Lewis Hall
    e Lewis Miley, Gabriel Magalhães e Gabriel Jesus): un id ESPN per persona. Poi riscarica le formazioni delle
    partite con quei giocatori e ricalcola le statistiche. Non fa niente se non trova errori."""
    names = {}
    boxes = [x.get("box") for x in MATCHES.values()] + [v.get("box") for v in (PRIOR.get("refCards") or {}).values()]
    for b in boxes:
        for eid, p in ((b or {}).get("players") or {}).items():
            if p.get("name"):
                names.setdefault(str(eid), p["name"])
    groups = {}
    for eid, cid in REG["espn"].items():
        if eid in names:
            groups.setdefault(str(cid), []).append(eid)
    fixed = set()
    for cid, eids in groups.items():   # due id ESPN nella stessa persona: per ESPN sono sempre due persone
        if len(eids) < 2:
            continue
        info = (REG["info"].get(cid) or {}).get("name")
        keep = max(eids, key=lambda e: (tokens(names[e]) == tokens(info), same_person(names[e], info)))
        for e in eids:
            if e != keep:
                new = str(-int(e))
                REG["espn"][e] = new
                REG["info"][new] = {"name": names[e], "teamId": None, "espnId": e}
                fixed.add(cid)
                log(f"Anagrafica: {names[e]} separato da {names[keep]} (erano uniti per errore)")
    # Understat: i collegamenti fatti con la regola vecchia si rifanno (canon_us li ricalcola alla prossima statistica)
    us_names = {}
    for y in (season_year(d), season_year(d) - 1):
        for p in ((statistiche.understat_parse(load_json(us_file(y), {})) or {}).get("players") or []) if us_file(y).exists() else []:
            us_names[str(p.get("usId"))] = p.get("name")
    for uid, cid in list(REG["us"].items()):
        if uid in us_names and (str(cid) in fixed or not same_person(us_names[uid], (REG["info"].get(str(cid)) or {}).get("name"))):
            del REG["us"][uid]
            fixed.add(str(cid))
    # un id Understat è una persona sola, e viceversa. Fino al 14/10/2026 due compagni con lo stesso cognome potevano
    # finire sullo stesso giocatore (Víctor e Iker Muñoz dell'Osasuna, Alex e Jacob Murphy del Newcastle): resta il nome
    # più vicino (a parità, quello della squadra del giocatore), gli altri si ricollegano con canon_us. Nei campionati
    # senza Understat l'id è quello di ESPN: deve essere lo stesso del giocatore
    us_fixed = 0
    if SHOT_XG:
        for uid, cid in list(REG["us"].items()):
            if str((REG["info"].get(str(cid)) or {}).get("espnId")) != str(uid):
                del REG["us"][uid]
                us_fixed += 1
    else:
        us_full = {}
        for y in (season_year(d), season_year(d) - 1):
            for p in ((statistiche.understat_parse(load_json(us_file(y), {})) or {}).get("players") or []) if us_file(y).exists() else []:
                us_full.setdefault(str(p.get("usId")), p)
        owners = {}
        for uid, cid in REG["us"].items():
            owners.setdefault(str(cid), []).append(uid)
        for cid, uids in owners.items():
            if len(uids) < 2:
                continue
            x = REG["info"].get(cid) or {}

            def fit(uid):
                u = us_full.get(uid)
                if not u:
                    return -1.0
                team = team_by_name(d, (u.get("team") or "").split(",")[-1])
                return reg_score(u.get("name"), x) + (1.0 if team and str(team) == str(x.get("teamId")) else 0.0)
            keep = max(uids, key=fit)
            for uid in uids:
                if uid != keep:
                    log(f"Anagrafica: Understat «{(us_full.get(uid) or {}).get('name')}» staccato da {x.get('name')} "
                        f"(collegato a «{(us_full.get(keep) or {}).get('name')}»)")
                    del REG["us"][uid]
                    us_fixed += 1
    # Opta, stessa regola (Liga: «Pablo García» del Racing era finito su Fran García del Betis, «José Ángel»
    # dell'Espanyol su José Ángel Carmona)
    opta = (load_json(OPTA_FILE, {}) or {}).get("players") or {}
    owners = {}
    for pid, cid in REG.get("opta", {}).items():
        owners.setdefault(str(cid), []).append(pid)
    for cid, pids in owners.items():
        if len(pids) < 2:
            continue
        x = REG["info"].get(cid) or {}

        def fit_o(pid):
            o = opta.get(pid)
            if not o:
                return -1.0
            team = team_by_name(d, o.get("team") or "")
            return reg_score(o.get("name"), x) + (1.0 if team and str(team) == str(x.get("teamId")) else 0.0)
        keep = max(pids, key=fit_o)
        for pid in pids:
            if pid != keep:
                log(f"Anagrafica: Opta «{(opta.get(pid) or {}).get('name')}» staccato da {x.get('name')}")
                del REG["opta"][pid]
                us_fixed += 1
    if us_fixed and not fixed:   # basta rifare le statistiche (anche della stagione scorsa), le formazioni sono giuste
        PRIOR["statsV"] = 1
        d["v"] = None
        save_json(REG_FILE, REG)
        save_json(PRIOR_FILE, PRIOR)
        return
    if not fixed:
        return
    # formazioni salvate con l'id sbagliato: si riscaricano da ESPN; statistiche di questa stagione e della scorsa da rifare
    for x in MATCHES.values():
        lu = x.get("lineups") or {}
        ids = {str(p.get("id")) for s in ("home", "away") for k in ("starters", "subs") for p in ((lu.get(s) or {}).get(k) or [])}
        if ids & fixed:
            x.pop("final", None)
            x["espnAt"] = 0
    PRIOR["statsV"] = 1
    d["v"] = None
    save_json(REG_FILE, REG)
    save_json(MATCH_FILE, MATCHES)
    save_json(PRIOR_FILE, PRIOR)
    VERSION["matches"] += 1


def role_clash(cid, us_pos):
    """Ruoli che non possono essere della stessa persona: portiere nell'anagrafica e difensore, centrocampista o
    attaccante su Understat, o il contrario («S», solo subentrato, non dice il ruolo). Esempio: l'«Álvaro Fernández»
    di Understat è il terzino Álvaro Carreras del Real Madrid, non il portiere omonimo di un'altra squadra."""
    parts = set((us_pos or "").split())
    gk, out = "GK" in parts, bool(parts & {"D", "M", "F"})
    reg_gk = (REG["info"].get(str(cid)) or {}).get("pos") == "G"
    return (reg_gk and out and not gk) or (not reg_gk and gk and not out)


def canon_us(u, team_of_title):
    """Giocatore Understat -> id dell'anagrafica: mai una persona con un ruolo incompatibile, né una già collegata a un
    altro id Understat (un id è una persona sola: «Víctor Muñoz» non può diventare il compagno «Iker Muñoz»). Nei
    campionati senza Understat (e in coppa) l'id è quello di ESPN, quindi il collegamento è esatto."""
    if SHOT_XG:
        cid = REG["espn"].get(str(u["usId"]))
        if cid is not None:
            REG["us"][u["usId"]] = cid
        return cid
    cid = REG["us"].get(u["usId"])
    if cid is not None and role_clash(cid, u.get("usPos")):   # collegamento sbagliato salvato prima del controllo
        REG["us"].pop(u["usId"], None)
        cid = None
    if cid is None:
        owned = {c for k, c in REG["us"].items() if k != u["usId"]}
        teams = [team_of_title(t) for t in (u.get("team") or "").split(",")]
        cid = reg_find(u["name"], teams, skip=owned)
        if cid is None or role_clash(cid, u.get("usPos")):
            cid = reg_find(u["name"], None, need=8.0, skip=owned)
        if cid is None or role_clash(cid, u.get("usPos")):
            return None
        REG["us"][u["usId"]] = cid
    return cid


def fc_fits(f, cid, alt=None):
    """Il giocatore di Fantacalcio.it f può essere cid? Portiere solo con portiere (Pietro Terracciano non è il
    difensore Filippo) e, se c'è, l'iniziale del nome giusta («Oyono J.» non è Anthony Oyono)."""
    x = REG["info"].get(str(cid)) or {}
    if x.get("pos") and (f.get("role") == "p") != (x["pos"] == "G"):
        return False
    m = re.search(r"\s([A-Z])\.$", f.get("name") or "")
    full = [t for t in (model.norm_tokens(n) for n in [x.get("name")] + list((alt or {}).get(str(cid)) or ())) if len(t) >= 2]
    return not m or not full or any(t[0].startswith(m.group(1).lower()) for t in full)


def canon_fc(f, tid, alt=None):
    """Giocatore di Fantacalcio.it (es. "Martinez L.") -> id dell'anagrafica: della sua squadra, non già collegato a un
    altro giocatore di Fantacalcio.it, e che torna con fc_fits. alt: altri nomi dello stesso giocatore (Understat:
    «Alhassane» è Abdel Rahim, «Zambo Anguissa» è Frank Anguissa)."""
    cid = REG["fc"].get(f["fcId"])
    if cid is not None and not fc_fits(f, cid, alt):   # collegamento sbagliato salvato prima del controllo
        REG["fc"].pop(f["fcId"], None)
        cid = None
    if cid is None:
        owned = {c for k, c in REG["fc"].items() if k != f["fcId"]}
        cands = [{"id": c, "name": n, "minutesPlayed": 0} for c, x in REG["info"].items()
                 if str(x.get("teamId")) == str(tid) and c not in owned and fc_fits(f, c, alt)
                 for n in [x.get("name")] + list((alt or {}).get(c) or ())
                 + ([" ".join([x.get("name") or ""] + list(alt[c]))] if (alt or {}).get(c) else [])]
        # «N'Dicka» = Ndicka, «Ederson D.S.» = Ederson
        for name in dict.fromkeys((f["name"], f["name"].replace("'", ""), re.sub(r"\s+(?:[A-Z]\.){2,}$", "", f["name"]))):
            p = model.match_roster_player({"name": name}, cands)
            if p:
                cid = REG["fc"][f["fcId"]] = p["id"]
                break
    return cid


US_FIELDS = ["minutesPlayed", "goals", "assists", "expectedGoals", "expectedAssists", "totalShots", "keyPasses",
             "yellowCards", "redCards", "npg", "npxG", "xGChain", "xGBuildup"]


def build_players(results, boxes, us, team_of_title, current):
    """Giocatori della stagione: partite ESPN + totali Understat (+ voti di Fantacalcio.it per quella in corso)."""
    out = {}
    for eid, s in statistiche.player_season(results, boxes).items():
        cid = canon_espn(eid, s.get("name"), s.get("teamId"), s.get("num"), s.get("espnPos"), move=current)
        x = REG["info"].get(cid) or {}
        p = out.setdefault(cid, {"id": int(cid), "name": x.get("name") or s.get("name")})
        p["teamId"] = int(s["teamId"])
        p["pos"] = x.get("pos") or pos_from_code(s.get("espnPos"))
        if current and x.get("num"):
            p["num"] = x["num"]
        for k, v in s.items():
            if isinstance(v, (int, float)) and not isinstance(v, bool):
                p[k] = p.get(k, 0) + v
        p["appearancesEspn"] = p.get("appearances", 0)
    def merge(cid, u):
        x = REG["info"].get(cid) or {}
        p = out.setdefault(cid, {"id": int(cid), "name": x.get("name") or u["name"], "pos": x.get("pos"),
                                 "teamId": int(team_of_title(u["team"].split(",")[-1]) or x.get("teamId") or 0)})
        p.update({k: u[k] for k in US_FIELDS if u.get(k) is not None})
        p["appearances"] = max(p.get("appearances") or 0, int(u.get("appearances") or 0))
        # i conti di Understat come li dà Understat (sources_compare li confronta con ESPN e le altre fonti)
        p["srcUs"] = [u.get("minutesPlayed"), u.get("goals"), u.get("assists"), u.get("yellowCards"), u.get("redCards")]
        linked.add(cid)

    linked, pending = set(), []
    for u in (us or {}).get("players") or []:
        cid = canon_us(u, team_of_title)
        if cid is None:
            pending.append(u)
        else:
            merge(cid, u)
    # Understat con un nome diverso da ESPN («Valde» e Víctor Valdepeñas, «Franck Zambo» e Frank Anguissa, «Djené
    # Dakonam» e Djené, «Álvaro Fernández» e Álvaro Carreras): nella stessa squadra, l'unico giocatore ESPN ancora senza
    # Understat con quasi gli stessi minuti (le due fonti differiscono di pochi minuti di recupero: 18 al massimo nei
    # collegamenti per nome) e un ruolo compatibile; a parità, quello del reparto indicato da Understat
    for u in pending:
        t, team = int(u.get("minutesPlayed") or 0), team_of_title((u.get("team") or "").split(",")[-1])
        if t < 30 or not team or "," in (u.get("team") or ""):
            continue
        owned = {c for k, c in REG["us"].items() if k != u["usId"]}
        near = [cid for cid, p in out.items() if cid not in linked and cid not in owned and str(p.get("teamId")) == str(team)
                and p.get("minutesEspn") is not None and abs(p["minutesEspn"] - t) <= max(20, .08 * t)
                and not role_clash(cid, u.get("usPos"))]
        same = [cid for cid in near if (out[cid].get("pos") or "") in (u.get("usPos") or "").split()]
        pick = near if len(near) == 1 else same if len(same) == 1 else []
        if pick:
            REG["us"][u["usId"]] = pick[0]
            merge(pick[0], u)
    if current:   # Opta: xG e xA diventano la media di Understat e Opta (due modelli indipendenti), più le statistiche nuove
        words = {}   # per gli omonimi di canon_opta, senza passare tutta l'anagrafica per ogni giocatore
        for c, x in REG["info"].items():
            for t in tokens(x.get("name")):
                words.setdefault((str(x.get("teamId")), t), set()).add(c)
        mins = {c: p.get("minutesEspn") for c, p in out.items()}
        tids = {}   # squadra di Opta -> id, cercata una volta sola
        opta_team = lambda t: tids[t] if t in tids else tids.setdefault(t, team_of_title(t))

        def add_opta(p, o):
            # Opta si aggiorna una volta al giorno, Understat e la cronaca ESPN entro un'ora: dopo una giornata Opta
            # può avere una partita in meno (Champions, 14/10/2026: Lautaro 0,32 xG su 90' per Opta, 2,92 su 180'
            # dalla cronaca). La media dei due xG si fa solo sugli stessi minuti; i numeri solo di Opta (contrasti,
            # duelli...) si dividono per i minuti di Opta (minutesOpta)
            om = o.get("mins_played")
            p["minutesOpta"] = om
            p["srcOpta"] = [om, o.get("goals"), o.get("assists"), o.get("yellows"), o.get("reds")]
            same = om is not None and abs(om - (p.get("minutesPlayed") or 0)) <= 45
            for k, ok in (("expectedGoals", "xg"), ("expectedAssists", "xa")):
                if o.get(ok) is not None:
                    p[k + "Opta"] = o[ok]
                    if p.get(k) is None:
                        p[k] = o[ok]
                    elif same:
                        p[k] = (p[k] + o[ok]) / 2
            for k, ok in (("chancesCreated", "chances_created"), ("tackles", "tackles"), ("interceptions", "interceptions"),
                          ("recoveries", "recoveries"), ("blocks", "blocks"), ("clearances", "clearances"),
                          ("aerialDuels", "aerial_duels"), ("aerialWon", "aerial_duels_won"), ("groundDuels", "ground_duels"),
                          ("groundWon", "ground_duels_won"), ("progCarries", "progressive_carries"),
                          ("goalsPrevented", "goals_prevented"), ("xgotConceded", "xgot_conceded"), ("foulsOpta", "fouls_commited")):
                if o.get(ok) is not None:
                    p[k] = o[ok]
        waiting = []
        for pid, o in ((load_json(OPTA_FILE, {}) or {}).get("players") or {}).items():
            cid = canon_opta(pid, o, opta_team, words, mins)
            if cid is None:
                waiting.append((pid, o))
            elif out.get(cid):
                add_opta(out[cid], o)
        # Opta con un nome diverso da ESPN (Shakhtar: «Pedro Henrique» e «Vinícius Tobias» sono i difensori che ESPN
        # chiama «Pedrinho» e «Vinicius Augusto»; Fiorentina: «Pote» è Pedro Gonçalves): come per Understat, nella stessa
        # squadra l'unico giocatore ESPN ancora senza Opta con quasi gli stessi minuti, le stesse presenze (contro le
        # coincidenze di minuti) e un ruolo compatibile (portiere con portiere); tra più candidati vale il ruolo di Opta,
        # poi gol e gialli uguali (i due difensori dello Shakhtar hanno giocato tutti i 270', uno solo ha segnato)
        taken = set(REG["opta"].values())
        for pid, o in waiting:
            t, team, role = int(o.get("mins_played") or 0), opta_team(o.get("team")), OPTA_POS.get(o.get("pos"))
            if t < 30 or not team:
                continue
            near = [cid for cid, p in out.items() if cid not in taken and str(p.get("teamId")) == str(team)
                    and p.get("minutesEspn") is not None and abs(p["minutesEspn"] - t) <= max(20, .08 * t)
                    and p.get("appearancesEspn") == o.get("apps") and (role is None or (p.get("pos") == "G") == (role == "G"))]
            fit = lambda c: (out[c].get("pos") != role, (out[c].get("goalsEspn") or 0) != (o.get("goals") or 0),
                             (out[c].get("yellowCardsEspn") or 0) != (o.get("yellows") or 0))
            low = min(map(fit, near), default=None)
            best = [c for c in near if fit(c) == low]
            if len(best) == 1:
                REG["opta"][pid] = best[0]
                taken.add(best[0])
                log(f"Anagrafica: Opta «{o['name']}» collegato a {out[best[0]].get('name')} con i minuti")
                add_opta(out[best[0]], o)
    # Understat che non torna con i tabellini ESPN (che tornano con la classifica): conta una partita due volte (Liga
    # 2026/27, Villarreal-Deportivo del 5/9: 9 presenze e 810 minuti in 8 partite, un gol in più a Pépé, Aubameyang e
    # Luismi Cruz). Se ci sono i tabellini di tutte le partite e un giocatore ha minuti (oltre 45) o gol diversi, valgono
    # i conti di ESPN e gli xG di Understat si riportano agli stessi minuti. Dove le due fonti tornano non cambia niente.
    all_boxes = all(boxes.get(str(e["id"])) for e in results if e.get("hs") is not None)
    for p in out.values():
        em, um = p.get("minutesEspn"), p.get("minutesPlayed")
        if not all_boxes or em is None or um is None:
            continue
        if abs(um - em) > 45 or (p.get("goals") or 0) != (p.get("goalsEspn") or 0):
            k = min(1.0, em / um) if um else 1.0
            for f in ("expectedGoals", "expectedAssists", "npxG", "keyPasses", "xGChain", "xGBuildup"):
                if p.get(f) is not None:
                    p[f] = p[f] * k
            # sugli stessi minuti di Opta la media dei due xG, saltata sopra perché i minuti di Understat non tornavano
            om = p.get("minutesOpta")
            if om is not None and abs(om - um) > 45 and abs(om - em) <= 45:
                for f in ("expectedGoals", "expectedAssists"):
                    if p.get(f) is not None and p.get(f + "Opta") is not None:
                        p[f] = (p[f] + p[f + "Opta"]) / 2
            if p.get("npg") is not None:
                p["npg"] = max(0, p["npg"] - ((p.get("goals") or 0) - (p.get("goalsEspn") or 0)))
            p.update(minutesPlayed=em, goals=p.get("goalsEspn", 0), assists=p.get("assistsEspn", 0), totalShots=p.get("shotsEspn", 0),
                     yellowCards=p.get("yellowCardsEspn", 0), redCards=p.get("redCardsEspn", 0),
                     appearances=p.get("appearancesEspn", p.get("appearances")))
    for p in out.values():
        # dove Understat non c'è, valgono i conti delle partite ESPN
        for k, src in (("minutesPlayed", "minutesEspn"), ("goals", "goalsEspn"), ("assists", "assistsEspn"),
                       ("totalShots", "shotsEspn"), ("yellowCards", "yellowCardsEspn"), ("redCards", "redCardsEspn")):
            if p.get(k) is None:
                p[k] = p.get(src, 0)
        p.setdefault("pos", "M")
        p["pos"] = p["pos"] or "M"
    return out


def espn_understat(d, y):
    """Campionato senza Understat: la stagione y (in corso o scorsa) nel formato di Understat, fatta con le partite ESPN
    (statistiche.understat_from_espn). La scorsa solo quando ci sono i tiri di quasi tutte le partite."""
    if y == season_year(d):
        results = [e for e in d.get("played") or [] if e.get("hs") is not None]
        shots = {str(e["id"]): letture.us_like(((MATCHES.get(str(e["id"])) or {}).get("ev") or {}).get("ev")) for e in results}
        boxes = {str(e["id"]): (MATCHES.get(str(e["id"])) or {}).get("box") for e in results}
        names = {str(r["team"]["id"]): r["team"]["name"] for r in (d.get("standings") or {}).get("total") or []}
    else:
        rc = PRIOR.get("refCards") or {}
        results = [x for x in PRIOR.get("results") or [] if x.get("hs") is not None]
        if not results or sum(1 for x in results if "shots" in rc.get(str(x.get("espn")), {})) < .95 * len(results):
            return None
        shots = {str(x["id"]): rc.get(str(x.get("espn")), {}).get("shots") for x in results}
        boxes = {str(x["id"]): rc.get(str(x.get("espn")), {}).get("box") for x in results}
        names = {str(r["team"]["id"]): r["team"]["name"] for r in (PRIOR.get("standings") or {}).get("total") or []}
    out = statistiche.understat_from_espn(results, {k: v for k, v in shots.items() if v}, boxes, names)
    return out if out["teams"] else None   # senza cronaca tiro per tiro (Turchia) niente xG: meglio nessun dato che zeri


def no_xg():
    """Campionato senza xG: né Understat né la cronaca tiro per tiro di ESPN (in Turchia ESPN ha solo gol, cartellini
    e cambi). I pronostici usano gol e tiri in porta, e le letture delle partite non ci sono."""
    return ESPN_XG and not us_file(season_year(STATE["data"] or {})).exists()


def team_extra_stats(d):
    """Statistiche di squadra che non sono nei tabellini: duelli aerei e a terra e palloni recuperati di Opta (i giocatori
    sommati per squadra) e, in Champions, i recuperi nella metà campo avversaria e i tocchi nell'area avversaria dei dati
    ufficiali UEFA. Servono allo stile di gioco (fisicità, pressing, baricentro)."""
    agg = {}
    for p in d.get("players") or []:
        a = agg.setdefault(str(p.get("teamId")), {})
        for k in ("aerialDuels", "aerialWon", "groundDuels", "groundWon", "recoveries"):
            if p.get(k) is not None:
                a[k] = a.get(k, 0) + p[k]
        if p.get("minutesOpta"):   # partite contate da Opta (che può averne una in meno): 990 minuti a partita
            a["optaN"] = a.get("optaN", 0) + p["minutesOpta"] / 990
    if CUP:
        for e in d.get("played") or []:
            t = ((MATCHES.get(str(e["id"])) or {}).get("uefa") or {}).get("t") or {}
            if not t.get("home") or not t.get("away"):
                continue
            for side, opp in (("home", "away"), ("away", "home")):
                a = agg.setdefault(str(e[side]["id"]), {})
                a["uefaN"] = a.get("uefaN", 0) + 1
                a["uefaReco"] = a.get("uefaReco", 0) + (t[side].get("reco") or 0)
                a["uefaBox"] = a.get("uefaBox", 0) + (t[side].get("box") or 0)
                a["uefaBoxA"] = a.get("uefaBoxA", 0) + (t[opp].get("box") or 0)
    for tid, o in (d.get("teams") or {}).items():
        st = o.setdefault("stats", {"matches": 0})
        for k in ("aerialDuels", "aerialWon", "groundDuels", "groundWon", "recoveries", "optaN", "uefaN", "uefaReco", "uefaBox", "uefaBoxA"):
            st.pop(k, None)
        st.update(agg.get(tid) or {})


def rebuild_stats(d):
    """Ricalcola le statistiche della stagione in corso (e della scorsa, quando ci sono tutte le partite)."""
    y = season_year(d)
    if SHOT_XG:
        cur = espn_understat(d, y)
        if cur:
            save_json(us_file(y), cur)
        else:
            us_file(y).unlink(missing_ok=True)
        if ESPN_XG and not us_file(y - 1).exists():
            prev = espn_understat(d, y - 1)
            if prev:
                save_json(us_file(y - 1), prev)
    us = statistiche.understat_parse(load_json(us_file(y), {})) if us_file(y).exists() else None
    fc = (load_json(FC_STATS_FILE, {}) or {}).get("players") or []
    results = [e for e in d.get("played") or [] if e.get("hs") is not None]
    venue_standings(d)
    boxes = {str(e["id"]): (MATCHES.get(str(e["id"])) or {}).get("box") for e in results}
    boxes = {k: v for k, v in boxes.items() if v}
    team_of = lambda title: team_by_name(d, title)
    if LEGA["understat"]:   # collegamenti Understat confermati (o corretti) dai minuti di ogni partita
        exact = us_links_by_minutes(d)
        us_names = {u["usId"]: u.get("name") for u in (us or {}).get("players") or []}
        conflicts = []
        for uid, cid in exact.items():
            old = REG["us"].get(uid)
            if old is not None and old != cid and reg_score(us_names.get(uid) or "", REG["info"].get(str(old)) or {}) >= 8:
                # nome identico nella stessa anagrafica: i minuti non lo scavalcano, si segnala
                conflicts.append(f"{us_names.get(uid)}: per nome è {(REG['info'].get(str(old)) or {}).get('name')}, "
                                 f"per minuti {(REG['info'].get(cid) or {}).get('name')}")
                continue
            if old != cid:
                rivals = [k for k, c in REG["us"].items() if c == cid and k != uid and k not in exact]
                strong = [k for k in rivals if reg_score(us_names.get(k) or "", REG["info"].get(cid) or {}) >= 8]
                if strong:   # il giocatore ha già un Understat con il suo stesso nome: si segnala, non si stacca
                    conflicts.append(f"{us_names.get(uid)}: per minuti è {(REG['info'].get(cid) or {}).get('name')}, "
                                     f"che per nome è già {us_names.get(strong[0])}")
                    continue
                for k in rivals:
                    del REG["us"][k]   # un altro id Understat sullo stesso giocatore: i minuti dicono di no
                log(f"Anagrafica: Understat {uid} collegato a {(REG['info'].get(cid) or {}).get('name')} con i minuti "
                    f"(prima {(REG['info'].get(str(REG['us'].get(uid))) or {}).get('name')})")
                REG["us"][uid] = cid
        played_us = sum(1 for u in (us or {}).get("players") or [] if (u.get("minutesPlayed") or 0) > 0)
        STATUS["usLinks"] = {"minutes": len(exact) - len(conflicts), "players": played_us, "conflicts": conflicts[:10]}
    ts = statistiche.team_season(results, boxes, (us or {}).get("teams"), team_of, (us or {}).get("players"))
    for tid, o in (d.get("teams") or {}).items():
        o["stats"] = ts.get(tid) or {"matches": 0}
    players = build_players(results, boxes, us, team_of, True)
    alt = {}   # nomi di Understat dei giocatori, per riconoscere quelli di Fantacalcio.it
    for u in (us or {}).get("players") or []:
        c = REG["us"].get(u["usId"])
        if c is not None and u.get("name") and u["name"] != (REG["info"].get(str(c)) or {}).get("name"):
            alt.setdefault(str(c), []).append(u["name"])
    for f in fc:
        tid = team_by_name(d, f["teamSlug"].replace("-", " "))
        cid = canon_fc(f, tid, alt) if tid else None
        if cid in players:
            voted = bool(f.get("pv"))   # senza partite a voto Fantacalcio.it scrive 0: non è un voto
            players[cid].update(rating=f.get("mv") if voted else None, ratingPV=f.get("pv"),
                                fantamedia=f.get("fm") if voted else None, fcRole=f.get("role"),
                                srcFc=[None, f.get("gol"), f.get("ass"), f.get("amm"), f.get("esp")])
    d["players"] = sorted(players.values(), key=lambda p: -(p.get("minutesPlayed") or 0))
    team_extra_stats(d)
    try:
        d["compare"] = sources_compare(d)
    except Exception as ex:
        log(f"Confronto tra le fonti non fatto: {errtxt(ex)}")
    if CUP:   # la base dei giocatori sono i loro campionati (al posto della stagione scorsa della competizione)
        PRIOR["players"] = cup_prior_players(d)
        PRIOR["statsV"] = 2
        save_json(PRIOR_FILE, PRIOR)
    d["v"] = DATA_VERSION
    d["fullAt"] = d["updatedAt"] = time.time()
    d["sources"] = {"matches": len(boxes), "played": len(results), "understat": bool(us), "fantacalcio": len(fc)}
    STATUS["statsAt"] = d["fullAt"]
    # stagione scorsa, con le stesse fonti (una volta sola, quando ci sono tutte le partite)
    rc = PRIOR.get("refCards") or {}
    pres = [x for x in PRIOR.get("results") or [] if x.get("hs") is not None]
    pbox = {str(x["id"]): (rc.get(str(x.get("espn"))) or {}).get("box") for x in pres}
    pbox = {k: v for k, v in pbox.items() if v}
    if PRIOR.get("statsV") != 2 and pres and len(pbox) >= .95 * len(pres) and us_file(y - 1).exists():
        pus = statistiche.understat_parse(load_json(us_file(y - 1), {}))
        pteams = {str(r["team"]["id"]): r["team"] for r in (PRIOR.get("standings") or {}).get("total") or []}

        def pteam_of(title):
            tk, best, bs = tokens(title), None, 0
            for tid, t in pteams.items():
                sc = len(tk & tokens(t.get("name"), t.get("fullName"), t.get("shortName")))
                if sc > bs:
                    best, bs = tid, sc
            return best
        PRIOR["teamsSofascore"] = PRIOR.get("teamsSofascore") or PRIOR.get("teams")
        PRIOR["playersSofascore"] = PRIOR.get("playersSofascore") or PRIOR.get("players")
        PRIOR["teams"] = statistiche.team_season(pres, pbox, pus["teams"], pteam_of, pus["players"])
        PRIOR["players"] = list(build_players(pres, pbox, pus, pteam_of, False).values())
        PRIOR["statsV"] = 2
        save_json(PRIOR_FILE, PRIOR)
        log(f"Stagione {PRIOR.get('year')} ricalcolata con ESPN e Understat: {len(PRIOR['players'])} giocatori")
    save_json(REG_FILE, REG)
    save_json(DATA_FILE, d)


def site_conf():
    """Dove pubblicare il sito. Su GitHub Actions: nel ramo "sito", già scaricato nella cartella del sito.
    Sul Mac: da sito.json, {"remote": ..., "branches": [...]}; con "cloud": true lo pubblica solo GitHub Actions."""
    if CLOUD:
        return {"branches": ["sito"]} if (SITE_ROOT / ".git").exists() else {}
    c = load_json(SITE_CONF, {}) or {}
    return c if c.get("remote") and not c.get("cloud") else {}


async def site_step():
    """Carica su GitHub la versione tascabile. Su GitHub Actions a ogni aggiornamento (ogni 30 minuti), anche
    senza novità; dal Mac solo quando c'è qualcosa di nuovo, al massimo ogni 15 minuti."""
    conf = site_conf()
    now = time.time()
    if not conf or (not CLOUD and now - EXTRA.get("siteAt", 0) < SITE_EVERY):
        return
    EXTRA["siteAt"] = now
    save_json(EXTRA_FILE, EXTRA)
    snap = load_json(SNAPSHOT_FILE, None)
    if not snap:
        return
    sig = sito.firma(snap)
    if sig == EXTRA.get("siteSig") and not CLOUD:
        return

    for tid in snap.get("teams") or {}:   # loghi che mancano ancora: da ESPN
        if (not (SITE_DIR / "loghi" / f"{tid}.png").exists() and img_url("team", tid)
                and not any((IMGDIR / f"team-{tid}.{ext}").exists() for ext in IMG_TYPES)):
            try:
                async with HTTP["espn"].get(img_url("team", tid), timeout=aiohttp.ClientTimeout(total=15)) as r:
                    if r.status == 200:
                        (IMGDIR / f"team-{tid}.png").write_bytes(await r.read())
            except (aiohttp.ClientError, asyncio.TimeoutError):
                pass

    def work():
        if conf.get("remote"):
            sito.collega(SITE_ROOT, conf["remote"])
        sito.prepara(SITE_DIR, snap, IMGDIR, LEGA["name"])
        return sito.pubblica(SITE_ROOT, conf.get("branches") or ["main"])
    ok, out = await asyncio.to_thread(work)
    if ok:
        EXTRA["siteSig"] = sig
        STATUS["siteAt"] = now
        STATUS.pop("err_sito", None)
        log("Sito aggiornato su GitHub")
    else:
        STATUS["err_sito"] = out[-300:]
        EXTRA["siteAt"] = now - SITE_EVERY + 180   # dopo un errore (es. token appena rinnovato) si riprova tra 3 minuti
        log(f"Sito non aggiornato: {out[-200:]}")
        gh_note(f"Sito non aggiornato: {out[-200:]}", "warning")
    save_json(EXTRA_FILE, EXTRA)


def stats_signature(d):
    rc = PRIOR.get("refCards") or {}
    return (sum(1 for e in d.get("played") or [] if (MATCHES.get(str(e["id"])) or {}).get("box")),
            EXTRA.get("usAt"), (load_json(FC_STATS_FILE, {}) or {}).get("at"), (load_json(OPTA_FILE, {}) or {}).get("at"), sum(1 for v in rc.values() if "box" in v) // 40,
            d.get("v"))


# ---------- ciclo di aggiornamento ----------

async def refresher():
    due = {"months": 0, "today": 0, "stand": 0}
    sig = None
    while True:
        now = time.time()
        d = STATE["data"]
        # 1. ESPN: calendario, live, classifica, formazioni (se ci sono gia' i dati di base)
        if d:
            try:
                window = in_window(d, now)
                ended = []
                if now >= due["months"]:
                    lt = time.localtime(now)
                    nm = (lt.tm_year + (lt.tm_mon == 12), lt.tm_mon % 12 + 1)
                    months = [f"{lt.tm_year}{lt.tm_mon:02d}", f"{nm[0]}{nm[1]:02d}"]
                    if CUP:   # in coppa tutti i mesi fino a giugno: il calendario intero della fase campionato e dei turni
                        k = lt.tm_year * 12 + lt.tm_mon - 1
                        end = (lt.tm_year + (lt.tm_mon >= 7)) * 12 + 5
                        months = [f"{m // 12}{m % 12 + 1:02d}" for m in range(k, end + 1)]
                    ended += await espn_schedule(d, months)
                    due["months"] = now + MONTHS_EVERY
                    due["today"] = now + (LIVE_EVERY if window else IDLE_EVERY)
                elif now >= due["today"]:
                    ended += await espn_schedule(d, [time.strftime("%Y%m%d", time.gmtime(now))])
                    due["today"] = now + (LIVE_EVERY if in_window(d, now) else IDLE_EVERY)
                if ended:
                    due["stand"] = 0
                    log("Partite terminate: " + ", ".join(f"{e['home']['name']} {e['hs']}-{e['as']} {e['away']['name']}" for e in ended))
                if now >= due["stand"]:
                    await espn_standings(d)
                    due["stand"] = now + (STAND_LIVE if in_window(d, now) else STAND_IDLE)
                # partite giocate prima dei mesi che si scaricano di solito (inizio stagione): una volta sola
                old = sorted({time.strftime("%Y%m", time.gmtime(e["start"])) for e in d.get("played") or []
                              if not e.get("espn")} - set(EXTRA.get("monthsDone") or []))
                if old and not window:
                    await espn_schedule(d, old[:1])
                    EXTRA.setdefault("monthsDone", []).append(old[0])
                    save_json(EXTRA_FILE, EXTRA)
                for e in summaries_due(d, now)[:(3 if window else 25 if CLOUD else 10)]:
                    if await espn_summary(e) and e.get("status") != "finished":
                        log(f"Formazioni ufficiali (ESPN): {e['home']['name']} - {e['away']['name']}")
                    VERSION["matches"] += 1
                for _ in range(3):
                    if PRIOR.get("complete") and not PRIOR.get("resultsDone"):
                        await espn_prior_results()
                await espn_prematch(d, now, 2 if window else 5)
                if prior_ref_pending():
                    await prior_ref_step(3 if window else 10)
                apply_ref_stats(d)
                await espn_rosters(d, now)
                save_json(MATCH_FILE, MATCHES)
                save_json(ESPN_FILE, ESPNMAP)
                STATUS.update(espnAt=time.time(), espnError=None)
                score = " | ".join(f"{e['home']['name']} {e['hs']}-{e['as']} {e['away']['name']}" for e in d["live"])
                if score != STATUS.get("_score"):
                    STATUS["_score"] = score
                    if score or STATUS.get("_hadLive"):
                        log(f"Live: {score or 'nessuna partita in corso'}")
                    STATUS["_hadLive"] = bool(score)
            except Exception as e:
                STATUS.update(espnError=errtxt(e)[:200])
                log(f"Errore ESPN: {errtxt(e)}")
                due["today"] = min(due["today"], now + 300)
        # 2. fonti di riserva: probabili formazioni, indisponibili e arbitri designati (fantacalcio.it), allenatori (Wikipedia)
        if d:
            steps = ((("fantacalcio.it", fantacalcio_step), ("designazioni", fc_referees), ("arbitri", fc_prior_referees))
                     if LEGA["fantacalcio"] else (("OneFootball", onefootball_step),))
            steps += ((("forza europea", mondo_step), ("UEFA", uefa_step), ("allenatori", cup_coaches)) if CUP
                      else (("Wikipedia", wiki_coaches),))
            for name, step in steps + (("foto", of_photos_step), ("Opta", opta_step), ("marcatori (Wikipedia)", wiki_scorers_step)):
                try:
                    await step(d, now)
                    STATUS.pop(f"err_{name}", None)
                except Exception as e:
                    STATUS[f"err_{name}"] = errtxt(e)[:200]
                    log(f"Errore {name}: {errtxt(e)}")
        # 3. statistiche: Understat e Fantacalcio.it, poi il ricalcolo con le partite ESPN
        if d:
            try:
                await sources_step(d, now)
                STATUS.pop("err_statistiche", None)
            except Exception as e:
                STATUS["err_statistiche"] = errtxt(e)[:200]
                log(f"Errore statistiche (Understat): {errtxt(e)}")
            try:
                await us_matches_step(d, now)
                STATUS.pop("err_letture", None)
            except Exception as e:
                STATUS["err_letture"] = errtxt(e)[:200]
                log(f"Errore tiri delle partite (Understat): {errtxt(e)}")
            if stats_signature(d) != sig:
                try:
                    rebuild_stats(d)
                    sig = stats_signature(d)
                except Exception as e:
                    STATUS["err_statistiche"] = errtxt(e)[:200]
                    log(f"Errore nel calcolo delle statistiche: {errtxt(e)}")
        if d:
            STATE["data"] = d
            save_json(DATA_FILE, d)
            update_history()
            try:
                snap = snapshot()
                save_json(SNAPSHOT_FILE, snap)
                ck = snap.get("checks") or {}
                if CLOUD and ck and not ck.get("ok"):   # nelle note dell'esecuzione di GitHub, leggibili senza accesso
                    gh_note(f"{LEGA['name']}: {ck.get('n')} controlli da guardare: " + "; ".join((ck.get("data") or []) + (ck.get("pred") or []))[:900], "warning")
            except Exception as e:
                log(f"Fotografia per la versione tascabile non salvata: {errtxt(e)}")
            try:
                await site_step()
            except Exception as e:
                STATUS["err_sito"] = errtxt(e)[:200]
                log(f"Errore sito: {errtxt(e)}")
        if CLOUD:
            return   # su GitHub un giro solo: il prossimo lo fa l'esecuzione programmata tra 30 minuti
        # 4. quando ricontrollare
        now = time.time()
        live = bool(d) and in_window(d, now)
        STATUS["mode"] = "live" if live else "attesa"
        targets = [due["today"], due["stand"], due["months"]]
        if d:
            k = next_kickoff(d, now)
            if k:
                targets.append(k)
            pend = summaries_due(d, now + LINEUP_EVERY)
            if pend:
                # formazioni delle partite giocate da recuperare: con ESPN si può andare più veloci
                targets.append(now + (120 if any(e.get("status") == "finished" for e in pend) else LINEUP_EVERY))
            if (PRIOR.get("complete") and not PRIOR.get("resultsDone")) or prior_ref_pending() or STATUS.get("_usPending"):
                targets.append(now + 120)
            if site_conf() and not CLOUD:
                targets.append(EXTRA.get("siteAt", 0) + SITE_EVERY)
            last_end = max((e["start"] + 2.25 * 3600 for e in d.get("played") or []), default=0)
            at = EXTRA.get("usAt", 0)
            targets.append(at + US_EVERY if not (at < last_end + 3600) else max(now, last_end + 3600))
        else:
            targets.append(now + 60)
        sleep = max(20, min(targets) - now)
        STATUS["nextCheck"] = now + sleep
        # si aspetta a passi di 30 secondi guardando l'ora vera: mentre il Mac è in stop il tempo di asyncio si ferma,
        # e al risveglio l'app aspetterebbe ancora tutto quello che mancava (il 02/10 è rimasta ferma dalle 4:55 alle 9:20)
        wake = now + sleep
        while time.time() < wake:
            await asyncio.sleep(min(30, wake - time.time()))


# ---------- aggiornamento su GitHub Actions (--cloud) ----------

CLOUD_START = time.time()


def source_errors():
    """Fonti che nell'ultimo giro hanno dato errore: {fonte: messaggio}."""
    errors = {k[4:]: v for k, v in STATUS.items() if k.startswith("err_")}
    if STATUS.get("espnError"):
        errors["ESPN"] = STATUS["espnError"]
    return errors


def gh_note(msg, level="error"):
    """Su GitHub Actions il messaggio finisce anche nelle note del run, che si leggono senza accedere a GitHub
    (i log completi invece solo con l'accesso)."""
    if CLOUD:
        msg = str(msg).replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
        print(f"::{level}::{msg}", flush=True)


def cloud_state_push():
    """Salva i dati nel ramo "dati" del repository: da lì riparte l'esecuzione successiva. Se nel frattempo
    qualcuno li ha cambiati non li sovrascrive (la prossima esecuzione riparte da quelli). Se GitHub non risponde
    riprova due volte."""
    save_json(CLOUD_FILE, {"at": time.time(), "start": CLOUD_START, "sito": EXTRA.get("siteSig"),
                           "errori": source_errors(), "codice": CODE_VERSION})
    for attempt in (1, 2, 3):
        ok, out = sito.pubblica(DATA_DIR, ["dati"], lease=True)
        if ok or "stale info" in out or attempt == 3:
            break
        log(f"Dati non salvati su GitHub, riprovo tra 20 secondi: {out[-300:]}")
        time.sleep(20)
    if ok:
        log("Dati salvati su GitHub")
    else:
        log(f"Dati non salvati su GitHub: {out[-300:]}")
        gh_note(f"Dati non salvati su GitHub: {out[-300:]}")
    return ok


def history_backup():
    """Una volta al giorno: copia dello storico dei pronostici nel ramo "storico", che tiene tutte le versioni.
    È l'unico dato che non si può ricreare, e nel ramo "dati" viene sovrascritto a ogni giro."""
    today = time.strftime("%Y-%m-%d")
    if EXTRA.get("storicoDay") == today or not HISTORY_FILE.exists():
        return
    branch = "storico" + (f"-{LEGA['dir']}" if LEGA["dir"] else "")   # un ramo per lega
    ok, out = sito.copia_storico(DATA_DIR, HISTORY_FILE, f"Storico dei pronostici del {time.strftime('%d/%m/%Y')}", branch=branch)
    if ok:
        EXTRA["storicoDay"] = today
        save_json(EXTRA_FILE, EXTRA)
        STATUS.pop("err_storico", None)
        log(out)
    else:
        STATUS["err_storico"] = out[-200:]
        log(f"Copia dello storico non salvata: {out[-200:]}")
        gh_note(f"Copia dello storico non salvata: {out[-200:]}", "warning")


async def cloud_main():
    """Un aggiornamento su GitHub Actions, senza pagina web: tutte le fonti, sito ripubblicato, salvataggio."""
    HTTP["espn"] = aiohttp.ClientSession()
    HTTP["web"] = aiohttp.ClientSession(headers={"User-Agent": UA, "Accept-Language": "it-IT,it;q=0.9"})
    try:
        STATE["data"] = load_json(DATA_FILE, None)
        if not STATE["data"] and LEGA["dir"]:   # lega nuova: si parte da ESPN
            STATE["data"] = await espn_bootstrap()
        if not STATE["data"]:
            log("Mancano i dati salvati (ramo \"dati\" del repository): niente da aggiornare")
            gh_note("Mancano i dati salvati (ramo \"dati\" del repository): niente da aggiornare")
            return 1
        reg_seed(STATE["data"])
        repair_registry(STATE["data"])
        refresh_squads(STATE["data"])
        venue_standings(STATE["data"])
        await refresher()
    finally:
        await HTTP["espn"].close()
        await HTTP["web"].close()
    await asyncio.to_thread(history_backup)
    FANTA_FILE.unlink(missing_ok=True)   # le rose del fanta stanno solo sul Mac: via dal repository pubblico
    return 0 if await asyncio.to_thread(cloud_state_push) else 1


# ---------- letture delle partite giocate ----------

READS = {"key": None}
# nomi brevi di ESPN che nel racconto suonano male
PRETTY = {"Man City": "Manchester City", "Man United": "Manchester United", "Spurs": "Tottenham", "C Palace": "Crystal Palace",
          "Nottm Forest": "Nottingham Forest", "Wolves": "Wolverhampton",
          # Liga: i nomi che in italiano si dicono così
          "Barcelona": "Barcellona", "Sevilla": "Siviglia", "Atlético": "Atlético Madrid", "Mallorca": "Maiorca",
          # Bundesliga e Ligue 1
          "Bayern": "Bayern Monaco", "Cologne": "Colonia", "Stuttgart": "Stoccarda", "Freiburg": "Friburgo",
          "Hamburg": "Amburgo", "Bremen": "Werder Brema", "Frankfurt": "Eintracht Francoforte", "RB Leipzig": "Lipsia",
          "Gladbach": "Borussia Mönchengladbach", "Dortmund": "Borussia Dortmund", "Leverkusen": "Bayer Leverkusen",
          "Marseille": "Marsiglia", "Lyon": "Lione", "Nice": "Nizza", "Strasbourg": "Strasburgo", "Toulouse": "Tolosa",
          "Le Havre AC": "Le Havre",
          # Eredivisie, Liga Portugal e Süper Lig
          "FC Twente": "Twente", "FC Groningen": "Groningen", "FC Utrecht": "Utrecht", "Fortuna": "Fortuna Sittard",
          "Sparta": "Sparta Rotterdam", "NEC": "NEC Nijmegen", "FC Porto": "Porto", "Vitória ": "Vitória Guimarães",
          "Vitória": "Vitória Guimarães", "Maritimo": "Marítimo", "FC Famalicao": "Famalicão", "Estrela": "Estrela Amadora",
          "Besiktas": "Beşiktaş", "Fenerbahce": "Fenerbahçe", "Caykur Rizespor": "Rizespor", "Istanbul BB": "Başakşehir",
          "Genclerbirli": "Gençlerbirliği", "Goztepe": "Göztepe", "Kasimpasa": "Kasımpaşa", "Eyupspor": "Eyüpspor",
          "Erzurum": "Erzurumspor"}


def team_names(d):
    return {str(r["team"]["id"]): PRETTY.get(r["team"]["name"], r["team"]["name"]) for r in d["standings"]["total"]}


def readings():
    """Letture di tutte le partite giocate (come sono nati i gol, come hanno giocato, perché il pronostico è andato
    così), profili di stagione delle squadre (come segnano e come subiscono) e riepilogo di ogni giornata.
    Si ricalcola solo quando cambiano partite, cronache, tiri o storico."""
    d = STATE["data"] or {}
    played = [e for e in d.get("played") or [] if e.get("hs") is not None]
    key = (len(played), VERSION["matches"], sum(1 for it in HISTORY.get("matches", {}).values() if it.get("result")))
    if READS.get("key") == key:
        return READS
    names = team_names(d) if d.get("standings") else {}
    mins = {p["id"]: int(p.get("minutesPlayed") or 0) for p in d.get("players") or []}
    base = []
    for e in played:
        x = MATCHES.get(str(e["id"])) or {}
        if not x.get("ev"):
            continue
        # senza i tiri (né Understat né la cronaca tiro per tiro: in Turchia ESPN ha solo gol, cartellini e cambi) la
        # lettura direbbe cose sbagliate («0 tiri», «partita combattuta»): meglio non farla
        if not x.get("us") and not any(v.get("k") in ("shot", "goal", "wood", "pens") for v in x["ev"].get("ev") or []):
            continue
        h, a = str(e["home"]["id"]), str(e["away"]["id"])
        it = HISTORY.get("matches", {}).get(str(e["id"])) or {}
        base.append((e, {"names": {"home": names.get(h, e["home"]["name"]), "away": names.get(a, e["away"]["name"])},
                         "hs": e["hs"], "as": e["as"], "box": x.get("box"), "ev": x.get("ev"), "us": x.get("us"),
                         "ppda": x.get("ppda"), "f": it.get("final") if it.get("result") else None, "ids": {"home": h, "away": a},
                         "ref": x.get("referee"), "lu": lineups_minutes(x.get("lineups"), mins), "uefa": x.get("uefa")}))
    prof = letture.profiles([{"ids": m["ids"], "goals": letture.goals_of(m), "us": m["us"], "ev": m["ev"]} for _, m in base])
    reads, by = {}, {}
    for e, m in base:
        try:
            r = letture.read_match(m, prof)
        except Exception as ex:
            log(f"Lettura di {e['home']['name']} - {e['away']['name']} non riuscita: {errtxt(ex)}")
            continue
        r.update({"id": e["id"], "round": e.get("round"), "start": e["start"], "home": m["ids"]["home"], "away": m["ids"]["away"],
                  "hs": e["hs"], "as": e["as"]})
        reads[str(e["id"])] = r
        by.setdefault(e.get("round"), []).append(r)
    played_in = {}
    for e in d.get("played") or []:
        played_in[e.get("round")] = played_in.get(e.get("round"), 0) + 1
    rounds = {}
    for rnd, lst in by.items():
        rs = letture.round_summary(lst, rnd)
        if rs:
            rs["of"] = played_in.get(rnd, len(lst)) + sum(1 for e in (d.get("live") or []) + (d.get("next") or []) if e.get("round") == rnd)
            rounds[rnd] = rs
    ranks = {k: letture.league_ranks(prof, k, "piazzati")[0] for k in ("xgf", "xga")}
    zr = letture.zone_ranks(prof)
    texts = {t: dict(letture.profile_text(p, zr.get(t), len(prof)), rk={"spf": ranks["xgf"].get(t), "spa": ranks["xga"].get(t)},
                     zone=zr.get(t)) for t, p in prof.items()}
    READS.update(key=key, reads=reads, prof=prof, texts=texts, rounds=rounds, names=names)
    return READS


def lineups_minutes(lu, mins):
    """Formazioni della partita con i minuti in stagione di ogni assente (per dire quali assenze pesavano)."""
    if not lu:
        return lu
    out = dict(lu)
    for s in ("home", "away"):
        if isinstance(lu.get(s), dict):
            out[s] = dict(lu[s], missing=[dict(x, min=mins.get(x.get("id"), 0)) for x in lu[s].get("missing") or []])
    return out


def keys_of(R, e):
    """Chiavi della partita dalle partite giocate (palle inattive, ripartenze, errori, gioco aereo, finali)."""
    try:
        return letture.keys_for(R["prof"], e["home"]["id"], e["away"]["id"], R["names"])
    except Exception as ex:
        log(f"Chiavi della partita non calcolate: {errtxt(ex)}")
        return []


def profiles_out(R):
    """Profili per le pagine delle squadre: numeri per categoria e frasi."""
    return {t: _r({"n": p["n"], "gf": p["gf"], "ga": p["ga"], "err": p["err"], "late": p["late"], "early": p["early"],
                   "xgf": {k: v / max(1, p.get("nus") or 1) for k, v in p["xgf"].items()},
                   "xga": {k: v / max(1, p.get("nus") or 1) for k, v in p["xga"].items()},
                   "fb": p["fb"], **R["texts"].get(t, {})}, 3) for t, p in R["prof"].items()}


def recent_rounds(R, k=2):
    return sorted((r for r in R["rounds"] if r is not None), reverse=True)[:k]


# ---------- fotografia per la versione tascabile ----------

def _r(x, nd=4):
    """Arrotonda i numeri per tenere leggera la fotografia."""
    if isinstance(x, float):
        return round(x, nd)
    if isinstance(x, dict):
        return {k: _r(v, nd) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [_r(v, nd) for v in x]
    return x


def snapshot():
    """Dati per il sito: classifica, pronostici completi, analisi delle squadre, storico. Il fanta no: sta solo sul Mac."""
    d, an = STATE["data"], analysis()
    A = an["A"]
    pub = model.public_analysis(A)
    teams = {tid: {"name": t["team"]["name"], "code": t["team"].get("code"), "color": t["team"].get("color"),
                   "arch": t["arch"]["name"], "second": (t["arch"].get("second") or {}).get("name"),
                   "coach": (t.get("coach") or {}).get("name"), "vacant": t.get("vacant"), "summary": t.get("summary"),
                   "dims": {k: round(v, 2) for k, v in t["dims"].items()},
                   "form": [f["r"] for f in t["ctx"]["form"][:5]],
                   "roles": (t.get("coachRoles") or {}).get("text"),
                   "scorer": (t["rel"].get("scorer") or {}).get("name"), "assister": (t["rel"].get("assister") or {}).get("name"),
                   "fullName": t["team"].get("fullName") or t["team"]["name"],
                   "full": _r({k: pub["teams"][tid].get(k) for k in ("n", "m", "rank", "pct", "z", "style", "rel", "formations", "rating",
                                                                     "dims", "dimsPrev", "arch", "changes", "coach", "coachRoles",
                                                                     "vacant")}
                              | {"formDet": [{"r": f["r"], "gf": f["gf"], "ga": f["ga"], "home": f["home"], "opp": f["opp"]["name"],
                                              "start": f["start"]} for f in t["ctx"]["form"][:5]],
                                 "s": {k: t["s"].get(k) for k in ("shots", "shotsAgainst", "corners", "cornersAgainst")}})}
             for tid, t in A["T"].items()}
    squads = {}
    for p in sorted(d.get("players") or [], key=lambda p: -(p.get("minutesPlayed") or 0)):
        lst = squads.setdefault(str(p.get("teamId")), [])
        if len(lst) < 16:
            lst.append(_r({"id": p["id"], "name": p.get("name"), "pos": p.get("pos"), "min": p.get("minutesPlayed"),
                           "g": p.get("goals"), "a": p.get("assists"), "xg": p.get("expectedGoals"), "xa": p.get("expectedAssists"),
                           "mv": p.get("rating"), "fm": p.get("fantamedia")}, 2))
    R = readings()
    fixtures = []
    for e in sorted(d.get("next") or [], key=lambda e: e["start"])[:20]:
        if e.get("status") != "notstarted" or str(e["home"]["id"]) not in A["T"] or str(e["away"]["id"]) not in A["T"]:
            continue
        P = model.predict(A, e["home"]["id"], e["away"]["id"], e, MATCHES.get(str(e["id"])))
        fixtures.append({"id": e["id"], "round": e.get("round"), "start": e["start"], "home": str(e["home"]["id"]),
                         "away": str(e["away"]["id"]), "p1": round(P["p1"], 3), "px": round(P["px"], 3), "p2": round(P["p2"], 3),
                         "lh": round(P["lh"], 2), "la": round(P["la"], 2), "over25": round(P["over25"], 3), "btts": round(P["btts"], 3),
                         "pick": P["pick"], "mk": P.get("market"),
                         "clash": [{"title": i["title"], "text": i["text"]} for i in P["style"]["items"] if i["kind"] == "rule"][:3],
                         "lineups": P["lineups"]["home"]["source"], "referee": (P.get("referee") or {}).get("name"),
                         "scorers": [{"name": p["name"], "team": str(t), "p": round(p["pGoal"], 2)}
                                     for t, key in ((e["home"]["id"], "home"), (e["away"]["id"], "away"))
                                     for p in sorted(P["players"][key], key=lambda p: -p["pGoal"])[:2]],
                         "keys": keys_of(R, e), "P": _r(P)})
    hist = sorted(HISTORY.get("matches", {}).values(), key=lambda it: -it["start"])[:30]
    rr = recent_rounds(R)
    hist_ids = {str(it["id"]) for it in hist}
    reads = {k: _r(v, 3) for k, v in R["reads"].items() if v.get("round") in rr or k in hist_ids}
    # tutti i giocatori con le statistiche della stagione: scheda del giocatore e ricerca
    players = [_r({"id": p["id"], "n": p.get("name"), "t": str(p.get("teamId")), "pos": p.get("pos"), "ap": p.get("appearances"),
                   "st": p.get("matchesStarted"), "min": p.get("minutesPlayed"), "g": p.get("goals"), "a": p.get("assists"),
                   "xg": p.get("expectedGoals"), "xa": p.get("expectedAssists"), "kp": p.get("keyPasses"), "sh": p.get("totalShots"),
                   "sot": p.get("shotsOnTarget"), "fo": p.get("fouls"), "fd": p.get("wasFouled"), "yc": p.get("yellowCards"),
                   "rc": p.get("redCards"), "sv": p.get("saves"), "mv": p.get("rating"), "fm": p.get("fantamedia"),
                   "pv": p.get("ratingPV"),
                   # Opta (Opta Analyst): contrasti, intercetti, recuperi, duelli, conduzioni progressive, gol evitati
                   "tk": p.get("tackles"), "itc": p.get("interceptions"), "rec": p.get("recoveries"), "gw": p.get("groundWon"),
                   "gd": p.get("groundDuels"), "aw": p.get("aerialWon"), "ad": p.get("aerialDuels"), "pcar": p.get("progCarries"),
                   "gp": p.get("goalsPrevented"), "xgot": p.get("xgotConceded"), "mo": p.get("minutesOpta"),
                   # portieri: gol subiti e porte inviolate (tabellini ESPN); numero di maglia
                   **({"gc": p.get("goalsConceded"), "cs": p.get("cleanSheet") or 0} if p.get("pos") == "G" else {}),
                   "num": p.get("num")}, 2)
               for p in d.get("players") or [] if (p.get("minutesPlayed") or 0) > 0]
    players = [{k: v for k, v in p.items() if v is not None} for p in players]   # più leggero: niente campi vuoti
    snap = {
        "generatedAt": time.time(), "statsAt": d.get("fullAt"), "season": d.get("season"), "errors": source_errors(),
        "standings": [{"team": str(r["team"]["id"]), "pos": r["pos"], "p": r["p"], "w": r["w"], "d": r["d"], "l": r["l"],
                       "gf": r["gf"], "ga": r["ga"], "pts": r["pts"], "zone": r.get("zone")} for r in d["standings"]["total"]],
        "teams": teams, "fixtures": fixtures, "squads": squads, "evidenza": an["evidenza"], "gustose": _r(an.get("gustose") or []),
        "metrics": pub["metrics"], "styleLabels": pub["styleLabels"], "N": len(A["T"]), "priorYear": A.get("priorYear"),
        "played": [{"id": e["id"], "home": str(e["home"]["id"]), "away": str(e["away"]["id"]), "hs": e["hs"], "as": e["as"],
                    "start": e["start"], "round": e.get("round")} for e in (d.get("played") or []) if e.get("hs") is not None],
        "live": [{"home": str(e["home"]["id"]), "away": str(e["away"]["id"]), "hs": e.get("hs"), "as": e.get("as"),
                  "clock": e.get("clock") or e.get("statusText")} for e in d.get("live") or []],
        "results": [{"home": str(e["home"]["id"]), "away": str(e["away"]["id"]), "hs": e["hs"], "as": e["as"],
                     "start": e["start"], "round": e.get("round")} for e in (d.get("played") or [])[:10]],
        "history": {"summary": model.history_summary(HISTORY),
                    "items": [{"id": it["id"], "round": it.get("round"), "home": str(it["home"]["id"]), "away": str(it["away"]["id"]),
                               "start": it["start"], "pick": (it.get("final") or it.get("latest") or {}).get("pick"),
                               "result": it.get("result"), "ok": (it.get("eval") or {}).get("pick"), "eval": it.get("eval"),
                               # com'è andata: il pronostico al calcio d'inizio e le statistiche vere
                               "f": it.get("final") if it.get("result") else None, "real": it.get("real")} for it in hist]},
        "players": players, "xpts": xpts_table(d),
        # letture delle partite: come sono nati i gol, come hanno giocato, perché il pronostico è andato così
        "reads": reads, "rounds": {str(k): R["rounds"][k] for k in rr}, "profiles": profiles_out(R),
        "league": {"yellowGame": _r(A["L"].get("yellowGame"), 2), "key": LEGA_KEY, "name": LEGA["name"], "dir": LEGA["dir"],
                   "fantacalcio": LEGA["fantacalcio"], "cup": CUP, "noXg": no_xg(), "xgEspn": ESPN_XG and not no_xg()},
        # coppa: nomi dei turni («Ottavi – andata»), proiezione della fase campionato, campionato di ogni squadra
        "roundNames": round_names(d), "proj": an.get("proj"),
        # coppa: dati ufficiali della UEFA (medie delle squadre e statistiche dei giocatori in Champions)
        **(uefa_out(d) if CUP else {}),
        # "minor": nel selettore stanno nel menu «Altri campionati» (richiesta dell'utente del 14/10)
        "leagues": [{"key": k, "name": v["name"], "dir": v["dir"], "minor": bool(v.get("minor"))} for k, v in LEGHE.items()],
    }
    # controlli automatici (controlli.py): incoerenze tra le parti, valori fuori scala, fonti a confronto
    try:
        snap["checks"] = STATE["checks"] = _r(dict(controlli.summary(d, snap, HISTORY, MATCHES, STATUS.get("usLinks")), at=time.time()), 3)
    except Exception as ex:
        log(f"Controlli automatici non fatti: {errtxt(ex)}")
    return snap


def xpts_table(d):
    """Punti attesi (xPts) di ogni squadra da Understat: quanti punti avrebbe fatto, in media, con le occasioni create e
    concesse in ogni partita. {squadra: {partite, punti, xPts, xG, xGA}}."""
    u = load_json(us_file(season_year(d)), {}) or {}
    out = {}
    for t in (u.get("teams") or {}).values():
        tid = team_by_name(d, t.get("title"))
        hs = t.get("history") or []
        if tid and hs:
            out[tid] = _r({"n": len(hs), "pts": sum(h.get("pts") or 0 for h in hs), "xpts": sum(model.num(h.get("xpts")) or 0 for h in hs),
                           "xg": sum(model.num(h.get("xG")) or 0 for h in hs), "xga": sum(model.num(h.get("xGA")) or 0 for h in hs)}, 2)
    return out


# ---------- server web ----------

def status_public():
    return {k: v for k, v in STATUS.items() if not k.startswith("_")}


def not_ready():
    return web.json_response({"loading": True, "status": status_public()}, status=503)


async def h_data(_):
    if not STATE["data"]:
        return not_ready()
    an = analysis()
    extras = {eid: {"confirmed": bool((x.get("lineups") or {}).get("confirmed")), "lineups": bool(x.get("lineups")),
                    "referee": (x.get("referee") or {}).get("name")}
              for eid, x in MATCHES.items() if not x.get("final")}
    R = readings()
    rr = recent_rounds(R, 3)
    return web.json_response({**STATE["data"], "analysis": an["pub"], "fixtures": an["fixtures"], "extras": extras,
                              "checks": STATE.get("checks"),
                              "reads": {k: v for k, v in R["reads"].items() if v.get("round") in rr},
                              "rounds": {str(k): R["rounds"][k] for k in rr}, "profiles": profiles_out(R),
                              "evidenza": an["evidenza"], "gustose": an.get("gustose") or [],
                              "league": {"key": LEGA_KEY, "name": LEGA["name"], "fantacalcio": LEGA["fantacalcio"], "cup": CUP,
                                         "noXg": no_xg(), "xgEspn": ESPN_XG and not no_xg()},
                              "roundNames": round_names(STATE["data"]), "proj": an.get("proj"),
                              **(uefa_out(STATE["data"]) if CUP else {}),
                              "leagues": [{"key": k, "name": v["name"], "port": v["port"], "minor": bool(v.get("minor"))}
                                          for k, v in LEGHE.items()],
                              "fantaTeams": len(FANTA.get("teams", [])), "status": status_public(), "now": time.time()})


def find_event(eid):
    d = STATE["data"]
    for lst in (d.get("live") or [], d.get("next") or [], d.get("played") or []):
        for e in lst:
            if str(e["id"]) == str(eid):
                return e
    return None


async def h_match(req):
    if not STATE["data"]:
        return not_ready()
    e = find_event(req.match_info["id"])
    A = analysis()["A"]
    if not e or str(e["home"]["id"]) not in A["T"] or str(e["away"]["id"]) not in A["T"]:
        raise web.HTTPNotFound()
    P = model.predict(A, e["home"]["id"], e["away"]["id"], e, MATCHES.get(str(e["id"])))
    P["keys"] = keys_of(readings(), e)
    return web.json_response(P)


# ---------- chat: domande a Claude sui dati dell'app (solo sul Mac) ----------

CHAT_DIR = DATA_DIR / "chat"   # i dati per Claude, in file che può solo leggere e cercare
CHAT = {"key": None, "lock": None}
# al posto delle istruzioni di Claude Code (pensate per programmare): solo queste, così ogni domanda pesa meno
CHAT_PROMPT = """Sei l'assistente di Serie A Live, l'app di statistiche e pronostici dell'utente; qui parli della {league} (stagione {season}).
Oggi è {today}. Rispondi in italiano, in modo chiaro e breve, per una persona che non è un tecnico.
I dati stanno in file JSON nella cartella {folder}. Parti da {folder}/indice.json per sapere cosa c'è, poi usa
Read (con il percorso completo) o Grep solo sui file che servono. Per un giocatore usa Grep su giocatori.jsonl con il
nome in minuscolo e senza accenti (es. "lautaro martinez", o solo il cognome): ogni riga è un giocatore completo.
Prima di dire che un dato manca, riprova la ricerca con una parte del nome. Usa SOLO quei dati: non inventare numeri né
notizie, e se un dato non c'è dillo. Quando dai un numero di' da dove viene (statistiche della stagione,
pronostico dell'app, fonte). Probabilità e dati attesi sono stime del modello dell'app, non certezze. Per le
partite di' se le formazioni sono probabili, stimate o ufficiali. Niente tabelle larghe: elenchi brevi o frasi."""
# domande che chiedono di ragionare (non solo di cercare un dato): per queste il modello più forte
CHAT_DEEP = re.compile(r"perch|convien|consigl|confront|analizz|spieg|schier|meglio|strateg|valut|differenz|rischi", re.I)


def slug(s):
    s = unicodedata.normalize("NFKD", str(s or "")).encode("ascii", "ignore").decode().lower()
    return re.sub(r"[^a-z0-9]+", "-", s).strip("-")


def chat_files():
    """Scrive (quando cambiano i dati) i file che Claude legge per rispondere: indice, classifica, partite,
    pronostici completi della prossima giornata, squadre, giocatori, in evidenza, fanta, storico."""
    an = analysis()
    R = readings()
    ck = (an["key"], R["key"])
    if CHAT["key"] == ck and (CHAT_DIR / "indice.json").exists():
        return
    d, A, pub = STATE["data"], an["A"], an["pub"]
    name = lambda tid: (A["T"].get(str(tid)) or {}).get("team", {}).get("name") or str(tid)
    CHAT_DIR.mkdir(parents=True, exist_ok=True)
    for f in list(CHAT_DIR.glob("*.json")) + list(CHAT_DIR.glob("*.jsonl")):
        f.unlink()
    files = {}

    def put(fname, obj, what):
        (CHAT_DIR / fname).write_text(json.dumps(_r(obj, 3), ensure_ascii=False, indent=1))
        files[fname] = what

    put("classifica.json", [{"pos": r["pos"], "squadra": r["team"]["name"], "punti": r["pts"], "giocate": r["p"], "V": r["w"],
                             "N": r["d"], "P": r["l"], "gol_fatti": r["gf"], "gol_subiti": r["ga"]} for r in d["standings"]["total"]],
        "classifica attuale")
    put("risultati.json", [{"giornata": e.get("round"), "data": time.strftime("%d/%m/%Y", time.localtime(e["start"])),
                            "partita": f"{e['home']['name']} - {e['away']['name']}", "risultato": f"{e['hs']}-{e['as']}"}
                           for e in d.get("played") or [] if e.get("hs") is not None], "risultati delle partite giocate")
    put("calendario.json", [{"giornata": e.get("round"), "data": time.strftime("%d/%m/%Y %H:%M", time.localtime(e["start"])),
                             "partita": f"{e['home']['name']} - {e['away']['name']}",
                             "pronostico": {k: (an["fixtures"].get(str(e["id"])) or {}).get(k) for k in ("p1", "px", "p2", "pick", "lh", "la")}}
                            for e in sorted(d.get("next") or [], key=lambda e: e["start"]) if e.get("status") == "notstarted"][:40],
        "prossime partite con il pronostico sintetico (p1/px/p2 = probabilità di 1, X, 2; lh/la = gol attesi)")
    for e, P in an.get("preds") or []:
        fname = f"partita-{slug(e['home']['name'])}-{slug(e['away']['name'])}.json"
        put(fname, {"partita": f"{e['home']['name']} - {e['away']['name']}", "giornata": e.get("round"),
                    "data": time.strftime("%d/%m/%Y %H:%M", time.localtime(e["start"])), "pronostico": P},
            f"pronostico completo di {e['home']['name']} - {e['away']['name']} (probabilità, gol attesi, formazioni e loro fonte, "
            f"statistiche previste per ogni giocatore, rischio giallo, scontro di stili, arbitro, assenti)")
    teams_players = {}
    for p in d.get("players") or []:
        teams_players.setdefault(str(p.get("teamId")), []).append(p)
    keys = ("minutesPlayed", "appearances", "matchesStarted", "goals", "assists", "expectedGoals", "expectedAssists", "totalShots",
            "shotsOnTarget", "keyPasses", "fouls", "wasFouled", "yellowCards", "redCards", "rating", "fantamedia",
            "tackles", "interceptions", "recoveries", "groundWon", "groundDuels", "aerialWon", "aerialDuels", "progCarries",
            "goalsPrevented", "xgotConceded")
    # un giocatore per riga, con il nome senza accenti in "cerca": una ricerca per nome restituisce subito tutte le sue
    # statistiche, senza leggere il file intero
    rows = [dict({"cerca": slug(p.get("name")).replace("-", " "), "nome": p.get("name"), "squadra": name(p.get("teamId")),
                  "ruolo": p.get("pos")}, **{k: _r(p.get(k), 3) for k in keys if p.get(k) is not None})
            for p in sorted(d.get("players") or [], key=lambda p: -(p.get("minutesPlayed") or 0))]
    (CHAT_DIR / "giocatori.jsonl").write_text("\n".join(json.dumps(r, ensure_ascii=False) for r in rows) + "\n")
    files["giocatori.jsonl"] = ("statistiche della stagione di tutti i giocatori, UNO PER RIGA (ruolo G/D/M/F; rating = media "
                                "voto Fantacalcio.it; fouls = falli fatti, wasFouled = falli subiti; tackles, interceptions, recoveries, duelli "
                                "(groundWon/groundDuels, aerialWon/aerialDuels), progCarries, goalsPrevented, xgotConceded = Opta; "
                                "expectedGoals ed expectedAssists = media di Understat e Opta). Per un giocatore usa Grep "
                                "con il nome in minuscolo e senza accenti (campo cerca), NON leggere il file intero")
    for tid, t in pub["teams"].items():
        put(f"squadra-{slug(name(tid))}.json", {"squadra": name(tid), "analisi": t,
                                                "giocatori": [p.get("name") for p in teams_players.get(tid, [])]},
            f"analisi di {name(tid)}: statistiche e posizione in lega, stile, allenatore, su chi fa affidamento, forma")
    put("in-evidenza.json", an["evidenza"], "giocatori in evidenza della prossima giornata (primi 10 per ogni statistica "
        "prevista, kp = chance create) e, in season, le classifiche della stagione con i dati reali (tot = totale, pg = a "
        "partita, solo con almeno minApps presenze)")
    put("metriche.json", pub["metrics"], "spiegazione delle statistiche di squadra (chiavi usate nei file delle squadre)")
    if FANTA.get("teams"):
        put("fanta.json", model.fanta(an["A"], FANTA, d, MATCHES, SQUADS.get("players", {})),
            "le squadre del fantacalcio dell'utente con i punti attesi dei giocatori")
    put("storico.json", {"riepilogo": model.history_summary(HISTORY), "partite": list(HISTORY.get("matches", {}).values())[-40:]},
        "storico dei pronostici dell'app e quanto ci ha azzeccato")
    rr = recent_rounds(R, 3)
    put("letture.json", {"giornate": {str(k): R["rounds"][k] for k in rr},
                         "partite": [dict(r, partita=f"{R['names'].get(r['home'], r['home'])} {r['hs']}-{r['as']} {R['names'].get(r['away'], r['away'])}")
                                     for r in sorted(R["reads"].values(), key=lambda r: -r["start"]) if r.get("round") in rr]},
        "letture delle ultime giornate: per ogni partita come sono nati i gol (why, lab = perché: errore, palla inattiva, "
        "transizione, seconda palla, difesa superata, prodezza), come hanno giocato le squadre (game), perché il pronostico "
        "è andato così (verdict) e i difetti che si ripetono (lessons); fonti: cronaca Opta di ESPN e tiri di Understat")
    put("profili-squadre.json", {R["names"].get(t, t): v for t, v in profiles_out(R).items()},
        "come segna e come subisce ogni squadra in stagione: gol per tipo (gf fatti, ga subiti: azione, corner, punizione, "
        "contropiede, rigore, autogol), errori individuali, gol nel finale, xG a partita per situazione (xgf/xga)")
    (CHAT_DIR / "indice.json").write_text(json.dumps({"aggiornato": time.strftime("%d/%m/%Y %H:%M"), "file": files},
                                                      ensure_ascii=False, indent=1))
    CHAT["key"] = ck


def claude_bin():
    """Claude Code: quello che si aggiorna da solo (~/.local/bin), altrimenti quello installato con l'app di Claude."""
    local = Path.home() / ".local" / "bin" / "claude"
    if local.exists():
        return str(local)
    found = sorted(Path.home().glob("Library/Application Support/Claude/claude-code/*/claude.app/Contents/MacOS/claude"),
                   key=lambda p: p.stat().st_mtime)
    return str(found[-1]) if found else shutil.which("claude")


async def h_chat(req):
    """Una domanda a Claude: legge solo i file della cartella chat e risponde. Risposte con il tuo account Claude."""
    if not STATE["data"]:
        return not_ready()
    body = await req.json()
    q = (body.get("q") or "").strip()[:2000]
    if not q:
        raise web.HTTPBadRequest()
    exe = claude_bin()
    if not exe:
        return web.json_response({"error": "Non trovo Claude su questo Mac: serve l'app di Claude."})
    CHAT["lock"] = CHAT["lock"] or asyncio.Lock()
    async with CHAT["lock"]:
        await asyncio.to_thread(chat_files)
        d = STATE["data"]
        prompt = CHAT_PROMPT.format(league=LEGA["name"], season=(d.get("season") or {}).get("year", ""), today=time.strftime("%d/%m/%Y %H:%M"),
                                    folder=CHAT_DIR)
        model_name = "sonnet" if CHAT_DEEP.search(q) or len(q) > 160 else "haiku"   # difficile se chiede di ragionare o è lunga
        args = [exe, "-p", q, "--output-format", "json", "--model", model_name, "--tools", "Read,Grep,Glob",
                "--allowedTools", "Read,Grep,Glob", "--system-prompt", prompt, "--strict-mcp-config"]
        if body.get("session") and re.fullmatch(r"[\w-]{8,64}", body["session"]):
            args += ["--resume", body["session"]]
        try:
            proc = await asyncio.create_subprocess_exec(*args, cwd=str(CHAT_DIR), stdin=asyncio.subprocess.DEVNULL,
                                                        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
            out, err = await asyncio.wait_for(proc.communicate(), timeout=180)
        except asyncio.TimeoutError:
            proc.kill()
            return web.json_response({"error": "Claude non ha risposto entro 3 minuti: riprova con una domanda più precisa."})
    try:
        res = json.loads(out.decode() or "{}")
    except ValueError:
        return web.json_response({"error": (err.decode() or out.decode() or "Risposta non leggibile")[-300:]})
    text = res.get("result") or ""
    if res.get("is_error"):
        if "login" in text.lower() or "logged in" in text.lower():
            return web.json_response({"error": "login", "detail": text})
        return web.json_response({"error": text[:300] or "Errore di Claude"})
    return web.json_response({"answer": text, "session": res.get("session_id"), "model": model_name})


async def h_predict(req):
    if not STATE["data"]:
        return not_ready()
    h, a = req.query.get("h", ""), req.query.get("a", "")
    A = analysis()["A"]
    if h not in A["T"] or a not in A["T"] or h == a:
        raise web.HTTPBadRequest()
    return web.json_response(model.predict(A, h, a))


async def h_history(_):
    items = sorted(HISTORY.get("matches", {}).values(), key=lambda it: -it["start"])
    R = readings()
    items = [dict(it, read=R["reads"].get(str(it["id"]))) for it in items]
    return web.json_response({"items": items, "summary": model.history_summary(HISTORY)})


async def h_fanta(_):
    if not STATE["data"]:
        return not_ready()
    return web.json_response(model.fanta(analysis()["A"], FANTA, STATE["data"], MATCHES, SQUADS.get("players", {})))


async def h_snapshot(_):
    if not STATE["data"]:
        return not_ready()
    return web.json_response(snapshot())


IMG_TYPES = {"webp": "image/webp", "png": "image/png", "jpg": "image/jpeg"}


async def h_img(req):
    kind, iid = req.match_info["kind"], req.match_info["id"]
    if kind not in ("team", "player", "manager") or not iid.lstrip("-").isdigit() or f"{kind}-{iid}" in IMG_MISSING:
        raise web.HTTPNotFound()
    headers = {"Cache-Control": "max-age=604800"}
    for ext, ct in IMG_TYPES.items():
        f = IMGDIR / f"{kind}-{iid}.{ext}"
        if f.exists():
            return web.Response(body=f.read_bytes(), content_type=ct, headers=headers)
    async with req.app["img_sem"]:
        try:
            url = img_url(kind, iid)
            if not url:
                IMG_MISSING.add(f"{kind}-{iid}")
                raise web.HTTPNotFound()
            async with HTTP["espn"].get(url, timeout=aiohttp.ClientTimeout(total=15)) as r:
                if r.status in (403, 404):
                    IMG_MISSING.add(f"{kind}-{iid}")
                    raise web.HTTPNotFound()
                if r.status != 200:
                    raise web.HTTPServiceUnavailable()
                ct = r.headers.get("Content-Type", "image/png").split(";")[0]
                body = await r.read()
        except (aiohttp.ClientError, asyncio.TimeoutError):
            raise web.HTTPNotFound()
    ext = {v: k for k, v in IMG_TYPES.items()}.get(ct, "png")
    (IMGDIR / f"{kind}-{iid}.{ext}").write_bytes(body)
    return web.Response(body=body, content_type=IMG_TYPES[ext], headers=headers)


def img_url(kind, iid):
    """Loghi e foto da ESPN (per gli allenatori ESPN non ha foto)."""
    if kind == "team":
        rev = {str(v): k for k, v in (ESPNMAP.get("teams") or {}).items()}
        return f"https://a.espncdn.com/i/teamlogos/soccer/500/{rev[iid]}.png" if iid in rev else None
    if kind == "player":   # prima la foto di OneFootball (ESPN non ha quella di molti giocatori, in Premier quasi nessuna)
        x = REG["info"].get(iid) or {}
        if x.get("ofId"):
            return fonti.OF_PHOTO.format(id=x["ofId"])
        return f"https://a.espncdn.com/i/headshots/soccer/players/full/{x['espnId']}.png" if x.get("espnId") else None
    return None


async def prefetch_logos():
    """Scarica in anticipo i loghi mancanti, uno alla volta."""
    d = STATE["data"]
    for tid in (d or {}).get("teams", {}):
        if not any((IMGDIR / f"team-{tid}.{ext}").exists() for ext in IMG_TYPES) and img_url("team", tid):
            try:
                async with HTTP["espn"].get(img_url("team", tid), timeout=aiohttp.ClientTimeout(total=15)) as r:
                    if r.status == 200:
                        ct = r.headers.get("Content-Type", "image/png").split(";")[0]
                        ext = {v: k for k, v in IMG_TYPES.items()}.get(ct, "png")
                        (IMGDIR / f"team-{tid}.{ext}").write_bytes(await r.read())
            except (aiohttp.ClientError, asyncio.TimeoutError):
                pass
            await asyncio.sleep(0.3)


async def h_version(_):
    return web.json_response({"app": "serie-a-live", "version": CODE_VERSION})


async def running_version():
    """Versione del server gia' in ascolto sulla porta, None se la porta e' usata da altro."""
    base = f"http://127.0.0.1:{PORT}"
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=5)) as s:
            async with s.get(base + "/api/version") as r:
                if r.status == 200:
                    return (await r.json()).get("version")
            async with s.get(base + "/api/data") as r:   # versioni precedenti, senza /api/version
                if r.status in (200, 503) and "status" in await r.json():
                    return "precedente"
    except Exception:
        pass
    return None


async def replace_old_server():
    """Chiude un Serie A Live di versione precedente. True se la porta si e' liberata."""
    pids = subprocess.run(["lsof", "-ti", f"tcp:{PORT}", "-sTCP:LISTEN"], capture_output=True, text=True).stdout.split()
    for pid in pids:
        try:
            os.kill(int(pid), signal.SIGTERM)
        except (ProcessLookupError, ValueError):
            pass
    for _ in range(40):
        await asyncio.sleep(.25)
        if not subprocess.run(["lsof", "-ti", f"tcp:{PORT}", "-sTCP:LISTEN"], capture_output=True, text=True).stdout.strip():
            return True
    return False


# logo ufficiale della lega, solo per la pagina del Mac (non va sul sito: è un marchio e il sito è pubblico). Icone di
# OneFootball, aggiornate (ESPN ha ancora il vecchio logo «Serie A TIM»).
LEAGUE_LOGO = {"serie-a": 13, "premier": 9, "liga": 10, "bundesliga": 1, "ligue1": 23, "eredivisie": 36, "portugal": 35,
               "superlig": 8, "champions": 5}


def png_alpha_bbox(data):
    """Riquadro della parte visibile di un PNG (non trasparente): (x0, y0, x1, y1), o None se il formato non è uno di
    quelli delle icone (8 bit, con tavolozza o RGBA, non interlacciato)."""
    import struct
    if data[:8] != b"\x89PNG\r\n\x1a\n":
        return None
    i, idat, trns, ihdr = 8, b"", b"", None
    while i < len(data):
        n = struct.unpack(">I", data[i:i + 4])[0]
        t, c = data[i + 4:i + 8], data[i + 8:i + 8 + n]
        i += 12 + n
        if t == b"IHDR":
            ihdr = struct.unpack(">IIBBBBB", c)
        elif t == b"IDAT":
            idat += c
        elif t == b"tRNS":
            trns = c
    if not ihdr or ihdr[2] != 8 or ihdr[3] not in (3, 6) or ihdr[6]:
        return None
    w, h, bpp = ihdr[0], ihdr[1], 1 if ihdr[3] == 3 else 4
    raw, stride, prev, p, pts = zlib.decompress(idat), w * bpp, bytearray(w * bpp), 0, []
    for y in range(h):
        f, line = raw[p], bytearray(raw[p + 1:p + 1 + stride])
        p += 1 + stride
        for x in range(stride):
            a, b, c = (line[x - bpp] if x >= bpp else 0), prev[x], (prev[x - bpp] if x >= bpp else 0)
            if f == 1:
                line[x] = (line[x] + a) & 255
            elif f == 2:
                line[x] = (line[x] + b) & 255
            elif f == 3:
                line[x] = (line[x] + (a + b) // 2) & 255
            elif f == 4:
                pa, pb, pc = abs(b - c), abs(a - c), abs(a + b - 2 * c)
                line[x] = (line[x] + (a if pa <= pb and pa <= pc else b if pb <= pc else c)) & 255
        prev = line
        for x in range(w):
            al = (trns[line[x]] if line[x] < len(trns) else 255) if bpp == 1 else line[x * 4 + 3]
            if al > 24:
                pts.append((x, y))
    if not pts:
        return None
    xs, ys = [q[0] for q in pts], [q[1] for q in pts]
    return min(xs), min(ys), max(xs), max(ys)


async def h_league_logo(_):
    """Logo ufficiale della lega senza i margini vuoti (le icone di OneFootball ne hanno molti: quella della Serie A
    occupa metà dell'immagine), così nella pagina del Mac si vede grande."""
    f = CACHE / "lega-logo-ritagliato.png"
    if not f.exists() and LEAGUE_LOGO.get(LEGA_KEY):
        try:
            url = f"https://images.onefootball.com/icons/leagueColoredCompetition/128/{LEAGUE_LOGO[LEGA_KEY]}.png"
            async with HTTP["web"].get(url, timeout=aiohttp.ClientTimeout(total=15)) as r:
                if r.status == 200 and r.headers.get("Content-Type", "").startswith("image/"):
                    data = await r.read()
                    src = CACHE / "lega-logo.png"
                    src.write_bytes(data)
                    bb = png_alpha_bbox(data)
                    if bb:   # quadrato intorno alla parte visibile, con un margine di 2 pixel
                        side = max(bb[2] - bb[0], bb[3] - bb[1]) + 5
                        cx, cy = (bb[0] + bb[2]) // 2, (bb[1] + bb[3]) // 2
                        subprocess.run(["sips", "-c", str(side), str(side), "--cropOffset", str(max(0, cy - side // 2)),
                                        str(max(0, cx - side // 2)), str(src), "--out", str(f)], capture_output=True)
                    if not f.exists():
                        f.write_bytes(data)
        except (aiohttp.ClientError, asyncio.TimeoutError):
            pass
    if not f.exists():
        raise web.HTTPNotFound()
    return web.Response(body=f.read_bytes(), content_type="image/png", headers={"Cache-Control": "max-age=86400"})


async def h_favicon(_):
    """Icona della scheda del browser: l'emblema della lega (emblemi.py), o il pallone dell'app ritagliato perché si
    veda anche piccolo."""
    emb = ROOT / "icone" / f"{LEGA_KEY}-192.png"
    if emb.exists():
        fav = CACHE / f"favicon-{LEGA_KEY}-64.png"
        if not fav.exists() or fav.stat().st_mtime < emb.stat().st_mtime:
            subprocess.run(["sips", "-z", "64", "64", str(emb), "--out", str(fav)], capture_output=True)
        if fav.exists():
            return web.Response(body=fav.read_bytes(), content_type="image/png", headers={"Cache-Control": "max-age=3600"})
    fav = CACHE / "favicon-64.png"
    src = ROOT / "Icona Serie A.png"
    if not fav.exists() and src.exists():
        tmp = CACHE / "favicon-crop.png"
        subprocess.run(["sips", "-c", "640", "640", str(src), "--out", str(tmp)], capture_output=True)
        subprocess.run(["sips", "-Z", "64", str(tmp), "--out", str(fav)], capture_output=True)
        tmp.unlink(missing_ok=True)
    if not fav.exists():
        raise web.HTTPNotFound()
    return web.Response(body=fav.read_bytes(), content_type="image/png", headers={"Cache-Control": "max-age=86400"})


async def h_index(_):
    return web.FileResponse(ROOT / "index.html", headers={"Cache-Control": "no-cache"})


async def main():
    offline = "--offline" in sys.argv
    url = f"http://127.0.0.1:{PORT}/"
    HTTP["espn"] = aiohttp.ClientSession()
    HTTP["web"] = aiohttp.ClientSession(headers={"User-Agent": UA, "Accept-Language": "it-IT,it;q=0.9"})
    app = web.Application()
    app.router.add_get("/", h_index)
    app.router.add_get("/favicon.png", h_favicon)
    app.router.add_get("/lega.png", h_league_logo)
    app.router.add_get("/favicon.ico", h_favicon)
    app.router.add_get("/api/data", h_data)
    app.router.add_get("/api/match/{id}", h_match)
    app.router.add_get("/api/predict", h_predict)
    app.router.add_get("/api/history", h_history)
    app.router.add_get("/api/fanta", h_fanta)
    app.router.add_get("/api/snapshot", h_snapshot)
    app.router.add_post("/api/chat", h_chat)
    app.router.add_get("/api/version", h_version)
    app.router.add_get("/img/{kind}/{id}", h_img)
    app["img_sem"] = asyncio.Semaphore(3)
    runner = web.AppRunner(app)
    await runner.setup()
    try:
        await web.TCPSite(runner, "127.0.0.1", PORT).start()
    except OSError:
        other = await running_version()
        if other and other != CODE_VERSION and await replace_old_server():
            print("Chiusa la versione precedente di Serie A Live: avvio quella aggiornata.", flush=True)
            await web.TCPSite(runner, "127.0.0.1", PORT).start()
        else:
            print(f"Serie A Live e' gia' in esecuzione su {url}" if other else
                  f"La porta {PORT} e' usata da un altro programma: chiudilo e riprova.", flush=True)
            if other and "--no-open" not in sys.argv:
                webbrowser.open(url)
            await HTTP["espn"].close()
            await HTTP["web"].close()
            return
    if not DATA_FILE.exists() and LEGA["dir"] and not offline:   # lega nuova: si parte da ESPN
        try:
            await espn_bootstrap()
        except Exception as e:
            log(f"Primo avvio non riuscito: {errtxt(e)}")
    if DATA_FILE.exists():
        STATE["data"] = load_json(DATA_FILE, None)
        if STATE["data"]:
            reg_seed(STATE["data"])
            repair_registry(STATE["data"])
            refresh_squads(STATE["data"])
            venue_standings(STATE["data"])
            STATUS["statsAt"] = STATE["data"].get("fullAt")
            log("Caricati gli ultimi dati salvati")
    print(f"{LEGA['name']} pronta su {url}  (chiudi questa finestra o premi Ctrl+C per fermarla)", flush=True)
    asyncio.ensure_future(prefetch_logos())
    if "--no-open" not in sys.argv:
        webbrowser.open(url)
    if offline:
        STATUS.update(mode="offline")
        log("Modalita' offline: nessuna richiesta esterna")
        await asyncio.Event().wait()
    else:
        await refresher()


if __name__ == "__main__":
    try:
        if CLOUD:
            try:
                code = asyncio.run(cloud_main())
            except Exception as e:
                gh_note(f"Aggiornamento interrotto da un errore: {type(e).__name__}: {e}"[:500])
                raise
            sys.exit(code)
        asyncio.run(main())
    except KeyboardInterrupt:
        pass
