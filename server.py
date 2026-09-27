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
        python server.py --cloud    (su GitHub Actions: nessuna pagina web; aggiorna i dati, pubblica il sito
                                     nel ramo "sito" e salva i dati nel ramo "dati", poi esce. Durante le
                                     partite resta acceso e aggiorna di continuo, al massimo 5 ore e mezza)
"""
import asyncio
import json
import os
import re
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

import fonti
import model
import sito
import statistiche

ROOT = Path(__file__).resolve().parent
# dati salvati e immagini stanno fuori dalla cartella dell'app, che puo' essere sincronizzata con iCloud
DATA_DIR = Path(os.environ.get("SERIEA_DATA_DIR") or Path.home() / "Library" / "Application Support" / "Serie A Live")
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
HISTORY_FILE = DATA_DIR / "history.json"   # storico dei pronostici: non sta in cache perche' non si puo' ricreare
FANTA_FILE = DATA_DIR / "fanta.json"       # rose del fantacalcio
SNAPSHOT_FILE = DATA_DIR / "fotografia.json"   # dati compatti per la versione tascabile (artefatto)
SITE_DIR = Path(os.environ.get("SERIEA_SITE_DIR") or DATA_DIR / "sito")   # sito su GitHub Pages (repository git locale)
SITE_CONF = DATA_DIR / "sito.json"            # {"remote": "https://github.com/<utente>/<repository>.git"}
CLOUD_FILE = DATA_DIR / "esecuzione.json"     # su GitHub Actions: com'è andato l'ultimo aggiornamento

PORT = int(os.environ.get("SERIEA_PORT", 8765))
ESPN_SITE = os.environ.get("SERIEA_ESPN", "https://site.api.espn.com/apis/site/v2/sports/soccer/ita.1")
ESPN_STAND = os.environ.get("SERIEA_ESPN_STAND", "https://site.api.espn.com/apis/v2/sports/soccer/ita.1/standings")
UA = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36"
WIKI_UA = "SerieALive/1.0 (https://github.com/pier21q/Serie-A)"   # come chiede Wikipedia ai programmi
DATA_VERSION = 4   # 4: statistiche da ESPN, Understat e Fantacalcio.it (non più Sofascore)

# ESPN
LIVE_EVERY, IDLE_EVERY = 60, 1800
STAND_LIVE, STAND_IDLE = 300, 7200
MONTHS_EVERY = 6 * 3600
FC_NEAR, FC_FAR = 3600, 4 * 3600   # probabili formazioni: ogni ora nei 2 giorni prima, ogni 4 ore nella settimana
WIKI_EVERY = 2 * 3600              # allenatori da Wikipedia: ogni 2 ore, per vedere presto esoneri e dimissioni
PRE_EVERY = 6 * 3600               # precedenti e arbitro designato (ESPN), nei 3 giorni prima
US_EVERY = 6 * 3600                # Understat e Fantacalcio.it: ogni 6 ore, e 1-3 ore dopo le partite
ROSTER_EVERY = 7 * 86400           # rose da ESPN: una volta a settimana
CLOUD = "--cloud" in sys.argv
# sito: dal Mac al massimo ogni 15 minuti; su GitHub ogni 7 (GitHub Pages ne regge al massimo 10 all'ora)
SITE_EVERY = (7 if CLOUD else 15) * 60
CLOUD_MAX = 5.5 * 3600             # un'esecuzione su GitHub dura al massimo 5 ore e mezza (il limite è 6)
CLOUD_GAP = 10 * 60                # se il prossimo controllo è più lontano, esce: ci pensa l'esecuzione successiva
STATE_EVERY = 20 * 60              # durante le partite i dati si salvano su GitHub ogni 20 minuti
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


def log(msg):
    print(f"[{time.strftime('%d/%m %H:%M:%S')}] {msg}", flush=True)


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
VERSION = {"matches": 0, "squads": 0, "coaches": 0}
# versione del codice: cambia a ogni modifica di server.py o model.py
CODE_VERSION = str(int(max((ROOT / f).stat().st_mtime for f in ("server.py", "model.py", "fonti.py", "statistiche.py", "sito.py"))))


def match_entry(e):
    x = MATCHES.setdefault(str(e["id"]), {})
    x.update(homeId=e["home"]["id"], awayId=e["away"]["id"], start=e["start"], round=e.get("round"))
    return x



# ---------- ESPN ----------

ALIASES = {"internazionale": "inter", "inter milan": "inter", "hellas verona": "verona"}
STOP = {"fc", "ac", "as", "ss", "us", "calcio", "sc", "cfc", "bc", "afc", "club", "ssc", "acf", "1913", "1907"}
ESPN_STATUS_IT = {"STATUS_FIRST_HALF": ("inprogress", "1° tempo", 6), "STATUS_HALFTIME": ("inprogress", "Intervallo", 31),
                  "STATUS_SECOND_HALF": ("inprogress", "2° tempo", 7), "STATUS_FULL_TIME": ("finished", "Finale", 100),
                  "STATUS_FINAL": ("finished", "Finale", 100), "STATUS_SCHEDULED": ("notstarted", "Da giocare", 0),
                  "STATUS_POSTPONED": ("postponed", "Rinviata", 60), "STATUS_CANCELED": ("postponed", "Annullata", 70),
                  "STATUS_ABANDONED": ("postponed", "Sospesa", 70)}
DEPTH = {"G": 0, "CD": 1, "CD-L": 1, "CD-R": 1, "RB": 1, "LB": 1, "RWB": 1.5, "LWB": 1.5, "DM": 1.6, "CDM": 1.6,
         "RM": 2, "LM": 2, "CM": 2, "CM-L": 2, "CM-R": 2, "AM": 3, "AM-L": 3, "AM-R": 3, "RW": 3.5, "LW": 3.5,
         "SS": 3.8, "CF-L": 3.8, "CF-R": 3.8, "CF": 4, "F": 4, "RF": 4, "LF": 4}


def tokens(*names):
    out = set()
    for n in names:
        s = unicodedata.normalize("NFD", (n or "").translate(model.TRANSLIT)).encode("ascii", "ignore").decode().lower()
        s = re.sub(r"[^a-z ]+", " ", s)
        for a, b in ALIASES.items():
            s = s.replace(a, b)
        out |= set(s.split()) - STOP
    return out


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
    return {"espn": str(e["id"]), "start": espn_time(e.get("date") or c.get("date")), "status": state, "statusText": text,
            "code": code, "clock": st.get("displayClock") if state == "inprogress" and code != 31 else None,
            "home": teams[h], "away": teams[a], "hs": score(comp["home"]), "as": score(comp["away"])}


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
        if not ev.get("round") and rounds:
            near = min(rounds, key=lambda r: abs(r[0] - ev["start"]))
            ev["round"] = near[1] if abs(near[0] - ev["start"]) < 3 * 86400 else None
        if was in ("notstarted", "inprogress", None) and ev["status"] == "finished" and base is not None:
            ended.append(ev)
        by_id[str(eid)] = ev
    now = time.time()
    allev = list(by_id.values())
    d["live"] = sorted([e for e in allev if e["status"] == "inprogress"], key=lambda e: e["start"])
    d["played"] = sorted([e for e in allev if e["status"] == "finished"], key=lambda e: -e["start"])[:120]
    d["next"] = sorted([e for e in allev if e["status"] in ("notstarted", "postponed") and e["start"] > now - 3 * 86400],
                       key=lambda e: e["start"])
    return ended


async def espn_schedule(d, months):
    """Calendario e risultati dei mesi indicati (formato AAAAMM) oppure di un giorno (AAAAMMGG)."""
    teams = cur_teams(d)
    evs = []
    for m in months:
        j = await espn_get(ESPN_SITE + "/scoreboard", dates=m)
        evs += [x for x in (espn_event(e, teams) for e in j.get("events", [])) if x]
    ended = merge_events(d, evs)
    d["updatedAt"] = time.time()
    return ended


async def espn_standings(d):
    teams = cur_teams(d)
    j = await espn_get(ESPN_STAND)
    ch = j.get("children") or []
    entries = ((ch[0].get("standings") if ch else j.get("standings")) or {}).get("entries") or []
    prev = {str(r["team"]["id"]): r for r in d["standings"].get("total") or []}
    rows = []
    for e in entries:
        sid = map_team(e.get("team") or {}, teams)
        if not sid:
            continue
        S = {s.get("name"): s.get("value") for s in e.get("stats") or []}
        num = lambda k: int(S.get(k) or 0)
        rows.append({"team": teams[sid], "pos": num("rank"), "p": num("gamesPlayed"), "w": num("wins"), "d": num("ties"),
                     "l": num("losses"), "gf": num("pointsFor"), "ga": num("pointsAgainst"), "pts": num("points"),
                     "zone": (prev.get(sid) or {}).get("zone") or ((e.get("note") or {}).get("description"))})
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
    if not tk or not pt:
        return 0.0
    last = max(tk, key=len)
    sc = 3.0 * len(tk & pt) + (2.0 if last in pt else 0)
    if jersey and str(x.get("num") or "") == str(jersey):
        sc += 2.5
    return sc


def reg_find(name, team_ids, jersey=None, need=4.0):
    """Giocatore dell'anagrafica con questo nome (nelle squadre indicate, o in tutte se None)."""
    teams = {str(t) for t in team_ids if t} if team_ids else None
    best, bs = None, 0.0
    for cid, x in REG["info"].items():
        if teams is not None and str(x.get("teamId")) not in teams:
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
        cid = reg_find(name, [team_id], jersey) if team_id else None
        if cid is None:
            cid = reg_find(name, None, None, need=8.0)   # arrivato da un'altra squadra
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


async def espn_summary(e):
    """Formazioni ufficiali e arbitro di una partita, da ESPN."""
    j = await espn_get(ESPN_SITE + "/summary", event=e["espn"])
    x = match_entry(e)
    x["espnAt"] = time.time()
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
        missing = "cards" not in x or "roles" not in x or "box" not in x
        if e.get("espn") and (not x.get("final") or missing) and now - x.get("espnAt", 0) >= (120 if missing else 3600):
            due.append((1, e))
    return [e for _, e in sorted(due, key=lambda t: t[0])]


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

ANALYSIS = {"key": None}


def analysis():
    d = STATE["data"]
    key = (d.get("updatedAt"), VERSION["matches"], VERSION["squads"], VERSION["coaches"], PRIOR.get("sid"),
           len(PRIOR.get("results") or []), len(FANTA.get("teams", [])),
           sum(1 for v in (PRIOR.get("refCards") or {}).values() if "roles" in v) // 20)
    if ANALYSIS["key"] != key:
        A = model.build(d, PRIOR, MATCHES, coaches=COACHES, role_rows=role_rows(d))
        fixtures = {}
        for e in d.get("next") or []:
            if e.get("status") == "notstarted" and str(e["home"]["id"]) in A["T"] and str(e["away"]["id"]) in A["T"]:
                fixtures[str(e["id"])] = model.summary(model.predict(A, e["home"]["id"], e["away"]["id"], e, MATCHES.get(str(e["id"]))))
        ANALYSIS.update(key=key, A=A, pub=model.public_analysis(A), fixtures=fixtures)
    return ANALYSIS


def update_history():
    try:
        if model.update_history(HISTORY, analysis()["A"], STATE["data"], MATCHES):
            save_json(HISTORY_FILE, HISTORY)
    except Exception as e:
        log(f"Storico pronostici non aggiornato: {e}")


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


def fc_player(name, cands):
    """Nome di fantacalcio.it (es. "Martinez L.") -> id dell'anagrafica; se non trovato, un id negativo stabile."""
    p = model.match_roster_player({"name": name}, cands)
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
    return fonti.parse_allenatori(await web_text(fonti.WIKI.format(a=year, b=year + 1), headers={"User-Agent": WIKI_UA}))


async def wiki_coaches(d, now):
    """Allenatori da Wikipedia, con le giornate in panchina (anche quelli della scorsa stagione)."""
    if now - EXTRA.get("wikiAt", 0) < WIKI_EVERY and EXTRA.get("wikiCur"):
        return
    EXTRA["wikiAt"] = now - WIKI_EVERY + 3600   # se va male, si riprova tra un'ora
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
        STATUS["err_Wikipedia inglese"] = str(e)[:200]
        log(f"Errore Wikipedia inglese: {e}")
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


def ref_stats(name):
    """Statistiche di un arbitro dalle partite ESPN di questa stagione e della scorsa."""
    tk = tokens(name)
    g = y = r = 0
    rows = [((x.get("referee") or {}).get("name"), x.get("cards")) for x in MATCHES.values()]
    rows += [(v.get("ref"), v.get("cards")) for v in (PRIOR.get("refCards") or {}).values()]
    for rn, c in rows:
        if rn and c and tokens(rn) == tk:
            g, y, r = g + 1, y + c["y"], r + c["r"]
    return {"name": name, "yellow": y, "red": r, "yellowRed": 0, "games": g, "source": "espn"} if g else {"name": name}


def apply_ref_stats(d):
    for e in (d.get("next") or []) + (d.get("live") or []):
        x = MATCHES.get(str(e["id"])) or {}
        ref = x.get("referee") or {}
        if ref.get("name") and (not ref.get("games") or ref.get("source") == "espn"):
            new = ref_stats(ref["name"])
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
        if (e.get("status") != "notstarted" or not e.get("espn") or not 1.5 < h <= 72
                or now - x.get("preAt", 0) < PRE_EVERY or (x.get("h2h") and (x.get("referee") or {}).get("name"))):
            continue
        j = await espn_get(ESPN_SITE + "/summary", event=e["espn"])
        x = match_entry(e)
        x["preAt"] = now
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


async def prior_ref_step(limit):
    """Arbitro e cartellini delle partite della scorsa stagione (una volta sola, poco alla volta)."""
    rc = PRIOR.setdefault("refCards", {})
    todo = [x["espn"] for x in PRIOR.get("results") or [] if x.get("espn") and "box" not in rc.get(str(x["espn"]), {})][:limit]
    for eid in todo:
        j = await espn_get(ESPN_SITE + "/summary", event=eid)
        rc[str(eid)] = {"ref": fonti.espn_referee(j), "cards": fonti.espn_cards(j), "roles": match_roles(j) or {},
                        "box": statistiche.box_from_summary(j) or {}}
    if todo:
        save_json(PRIOR_FILE, PRIOR)
    return len(todo)


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


async def sources_step(d, now):
    """Understat (xG, xA, pressing, minuti) e Fantacalcio.it (media voto): ogni 6 ore e dopo le partite."""
    last_end = max((e["start"] + 2.25 * 3600 for e in d.get("played") or []), default=0)
    at = EXTRA.get("usAt", 0)
    if now - at < US_EVERY and not (at < last_end + 3600 <= now):
        return False
    EXTRA["usAt"] = now - US_EVERY + 1800   # se va male, si riprova tra mezz'ora
    save_json(EXTRA_FILE, EXTRA)
    y = season_year(d)
    save_json(us_file(y), await us_get(y))
    if not us_file(y - 1).exists():
        save_json(us_file(y - 1), await us_get(y - 1))
    STATUS["usAt"] = time.time()
    try:
        rows = statistiche.parse_fc_stats(await web_text(statistiche.FC_STATS))
        if rows:
            save_json(FC_STATS_FILE, {"at": time.time(), "players": rows})
            STATUS["fcStatsAt"] = time.time()
    except Exception as e:
        log(f"Errore Fantacalcio.it (statistiche): {e}")
    EXTRA["usAt"] = now
    save_json(EXTRA_FILE, EXTRA)
    log("Statistiche aggiornate da Understat e Fantacalcio.it")
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


def canon_us(u, team_of_title):
    """Giocatore Understat -> id dell'anagrafica."""
    cid = REG["us"].get(u["usId"])
    if cid is None:
        teams = [team_of_title(t) for t in (u.get("team") or "").split(",")]
        cid = reg_find(u["name"], teams) or reg_find(u["name"], None, need=8.0)
        if cid is None:
            return None
        REG["us"][u["usId"]] = cid
    return cid


def canon_fc(f, tid):
    """Giocatore di Fantacalcio.it (es. "Martinez L.") -> id dell'anagrafica."""
    cid = REG["fc"].get(f["fcId"])
    if cid is None:
        cands = [{"id": c, "name": x.get("name"), "minutesPlayed": 0} for c, x in REG["info"].items()
                 if str(x.get("teamId")) == str(tid)]
        p = model.match_roster_player({"name": f["name"]}, cands)
        if not p:
            return None
        cid = REG["fc"][f["fcId"]] = p["id"]
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
    for u in (us or {}).get("players") or []:
        cid = canon_us(u, team_of_title)
        if cid is None:
            continue
        x = REG["info"].get(cid) or {}
        p = out.setdefault(cid, {"id": int(cid), "name": x.get("name") or u["name"], "pos": x.get("pos"),
                                 "teamId": int(team_of_title(u["team"].split(",")[-1]) or x.get("teamId") or 0)})
        p.update({k: u[k] for k in US_FIELDS if u.get(k) is not None})
        p["appearances"] = max(p.get("appearances") or 0, int(u.get("appearances") or 0))
    for p in out.values():
        # dove Understat non c'è, valgono i conti delle partite ESPN
        for k, src in (("minutesPlayed", "minutesEspn"), ("goals", "goalsEspn"), ("assists", "assistsEspn"),
                       ("totalShots", "shotsEspn"), ("yellowCards", "yellowCardsEspn"), ("redCards", "redCardsEspn")):
            if p.get(k) is None:
                p[k] = p.get(src, 0)
        p.setdefault("pos", "M")
        p["pos"] = p["pos"] or "M"
    return out


def rebuild_stats(d):
    """Ricalcola le statistiche della stagione in corso (e della scorsa, quando ci sono tutte le partite)."""
    y = season_year(d)
    us = statistiche.understat_parse(load_json(us_file(y), {})) if us_file(y).exists() else None
    fc = (load_json(FC_STATS_FILE, {}) or {}).get("players") or []
    results = [e for e in d.get("played") or [] if e.get("hs") is not None]
    boxes = {str(e["id"]): (MATCHES.get(str(e["id"])) or {}).get("box") for e in results}
    boxes = {k: v for k, v in boxes.items() if v}
    team_of = lambda title: team_by_name(d, title)
    ts = statistiche.team_season(results, boxes, (us or {}).get("teams"), team_of, (us or {}).get("players"))
    for tid, o in (d.get("teams") or {}).items():
        o["stats"] = ts.get(tid) or {"matches": 0}
    players = build_players(results, boxes, us, team_of, True)
    for f in fc:
        tid = team_by_name(d, f["teamSlug"].replace("-", " "))
        cid = canon_fc(f, tid) if tid else None
        if cid in players:
            players[cid].update(rating=f.get("mv"), ratingPV=f.get("pv"), fantamedia=f.get("fm"), fcRole=f.get("role"))
    d["players"] = sorted(players.values(), key=lambda p: -(p.get("minutesPlayed") or 0))
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
        return {"branches": ["sito"]} if (SITE_DIR / ".git").exists() else {}
    c = load_json(SITE_CONF, {}) or {}
    return c if c.get("remote") and not c.get("cloud") else {}


async def site_step(gap=SITE_EVERY):
    """Carica su GitHub la versione tascabile quando ci sono novità (al massimo ogni SITE_EVERY)."""
    conf = site_conf()
    now = time.time()
    if not conf or now - EXTRA.get("siteAt", 0) < gap:
        return
    EXTRA["siteAt"] = now
    save_json(EXTRA_FILE, EXTRA)
    snap = load_json(SNAPSHOT_FILE, None)
    if not snap:
        return
    sig = sito.firma(snap)
    if sig == EXTRA.get("siteSig"):
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
            sito.collega(SITE_DIR, conf["remote"])
        sito.prepara(SITE_DIR, snap, IMGDIR)
        return sito.pubblica(SITE_DIR, conf.get("branches") or ["main"])
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
    save_json(EXTRA_FILE, EXTRA)


def stats_signature(d):
    rc = PRIOR.get("refCards") or {}
    return (sum(1 for e in d.get("played") or [] if (MATCHES.get(str(e["id"])) or {}).get("box")),
            EXTRA.get("usAt"), (load_json(FC_STATS_FILE, {}) or {}).get("at"), sum(1 for v in rc.values() if "box" in v) // 40,
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
                    ended += await espn_schedule(d, [f"{lt.tm_year}{lt.tm_mon:02d}", f"{nm[0]}{nm[1]:02d}"])
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
                for e in summaries_due(d, now)[:(3 if window else 10)]:
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
                STATUS.update(espnError=str(e)[:200])
                log(f"Errore ESPN: {e}")
                due["today"] = min(due["today"], now + 300)
        # 2. fonti di riserva: probabili formazioni e indisponibili (fantacalcio.it), allenatori (Wikipedia)
        if d:
            for name, step in (("fantacalcio.it", fantacalcio_step), ("Wikipedia", wiki_coaches)):
                try:
                    await step(d, now)
                    STATUS.pop(f"err_{name}", None)
                except Exception as e:
                    STATUS[f"err_{name}"] = str(e)[:200]
                    log(f"Errore {name}: {e}")
        # 3. statistiche: Understat e Fantacalcio.it, poi il ricalcolo con le partite ESPN
        if d:
            try:
                await sources_step(d, now)
                STATUS.pop("err_statistiche", None)
            except Exception as e:
                STATUS["err_statistiche"] = str(e)[:200]
                log(f"Errore statistiche (Understat): {e}")
            if stats_signature(d) != sig:
                try:
                    rebuild_stats(d)
                    sig = stats_signature(d)
                except Exception as e:
                    STATUS["err_statistiche"] = str(e)[:200]
                    log(f"Errore nel calcolo delle statistiche: {e}")
        if d:
            STATE["data"] = d
            save_json(DATA_FILE, d)
            update_history()
            try:
                save_json(SNAPSHOT_FILE, snapshot())
            except Exception as e:
                log(f"Fotografia per la versione tascabile non salvata: {e}")
            try:
                await site_step()
            except Exception as e:
                STATUS["err_sito"] = str(e)[:200]
                log(f"Errore sito: {e}")
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
            if (PRIOR.get("complete") and not PRIOR.get("resultsDone")) or prior_ref_pending():
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
        if CLOUD:
            CLOUD_RUN["giri"] += 1
            # su GitHub: se non c'è niente da fare a breve si esce, ci pensa l'esecuzione programmata successiva
            if not d or sleep > CLOUD_GAP or now + sleep - CLOUD_RUN["start"] > CLOUD_MAX or CLOUD_RUN.get("stop"):
                return
            if now - CLOUD_RUN["stateAt"] > STATE_EVERY:
                await asyncio.to_thread(cloud_state_push)
        await asyncio.sleep(sleep)


# ---------- aggiornamento su GitHub Actions (--cloud) ----------

CLOUD_RUN = {"start": time.time(), "stateAt": time.time(), "giri": 0}


def cloud_state_push():
    """Salva i dati nel ramo "dati" del repository: da lì riparte l'esecuzione successiva."""
    errors = {k[4:]: v for k, v in STATUS.items() if k.startswith("err_")}
    if STATUS.get("espnError"):
        errors["ESPN"] = STATUS["espnError"]
    save_json(CLOUD_FILE, {"at": time.time(), "start": CLOUD_RUN["start"], "giri": CLOUD_RUN["giri"],
                           "sito": EXTRA.get("siteSig"), "errori": errors, "codice": CODE_VERSION})
    ok, out = sito.pubblica(DATA_DIR, ["dati"], lease=True)
    CLOUD_RUN["stateAt"] = time.time()
    if ok:
        log("Dati salvati su GitHub")
    else:
        CLOUD_RUN["stop"] = True   # qualcuno ha cambiato i dati nel frattempo: si riparte da quelli
        log(f"Dati non salvati su GitHub: {out[-300:]}")
    return ok


async def cloud_main():
    """Un aggiornamento su GitHub Actions, senza pagina web: dati, sito se è cambiato qualcosa, salvataggio."""
    HTTP["espn"] = aiohttp.ClientSession()
    HTTP["web"] = aiohttp.ClientSession(headers={"User-Agent": UA, "Accept-Language": "it-IT,it;q=0.9"})
    try:
        STATE["data"] = load_json(DATA_FILE, None)
        if not STATE["data"]:
            log("Mancano i dati salvati (ramo \"dati\" del repository): niente da aggiornare")
            return 1
        reg_seed(STATE["data"])
        refresh_squads(STATE["data"])
        await refresher()
        if not CLOUD_RUN.get("stop"):
            try:
                await site_step(gap=180)   # l'ultima novità prima di uscire (es. il risultato finale)
            except Exception as e:
                STATUS["err_sito"] = str(e)[:200]
                log(f"Errore sito: {e}")
    finally:
        await HTTP["espn"].close()
        await HTTP["web"].close()
    if CLOUD_RUN.get("stop"):
        return 1
    return 0 if await asyncio.to_thread(cloud_state_push) else 1


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
    """Dati per l'artefatto: classifica, pronostici completi, analisi delle squadre, fantacalcio, storico."""
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
    fixtures = []
    for e in sorted(d.get("next") or [], key=lambda e: e["start"])[:20]:
        if e.get("status") != "notstarted" or str(e["home"]["id"]) not in A["T"] or str(e["away"]["id"]) not in A["T"]:
            continue
        P = model.predict(A, e["home"]["id"], e["away"]["id"], e, MATCHES.get(str(e["id"])))
        fixtures.append({"id": e["id"], "round": e.get("round"), "start": e["start"], "home": str(e["home"]["id"]),
                         "away": str(e["away"]["id"]), "p1": round(P["p1"], 3), "px": round(P["px"], 3), "p2": round(P["p2"], 3),
                         "lh": round(P["lh"], 2), "la": round(P["la"], 2), "over25": round(P["over25"], 3), "btts": round(P["btts"], 3),
                         "pick": P["pick"], "clash": [{"title": i["title"], "text": i["text"]} for i in P["style"]["items"] if i["kind"] == "rule"][:3],
                         "lineups": P["lineups"]["home"]["source"], "referee": (P.get("referee") or {}).get("name"),
                         "scorers": [{"name": p["name"], "team": str(t), "p": round(p["pGoal"], 2)}
                                     for t, key in ((e["home"]["id"], "home"), (e["away"]["id"], "away"))
                                     for p in sorted(P["players"][key], key=lambda p: -p["pGoal"])[:2]],
                         "P": _r(P)})
    fv = model.fanta(A, FANTA, d, MATCHES, SQUADS.get("players", {})) if FANTA.get("teams") else {"teams": []}
    fanta = [{"league": t["league"], "name": t["name"], "xi": t["xi"],
              "players": [{k: p.get(k) for k in ("name", "role", "team", "status", "pts", "pGoal", "pYellow", "pCS")}
                          | {"opp": (p.get("next") or {}).get("opp", {}).get("name"), "home": (p.get("next") or {}).get("home")}
                          for p in t["players"]]} for t in fv["teams"]]
    hist = sorted(HISTORY.get("matches", {}).values(), key=lambda it: -it["start"])[:30]
    return {
        "generatedAt": time.time(), "statsAt": d.get("fullAt"), "season": d.get("season"),
        "standings": [{"team": str(r["team"]["id"]), "pos": r["pos"], "p": r["p"], "w": r["w"], "d": r["d"], "l": r["l"],
                       "gf": r["gf"], "ga": r["ga"], "pts": r["pts"], "zone": r.get("zone")} for r in d["standings"]["total"]],
        "teams": teams, "fixtures": fixtures, "squads": squads,
        "metrics": pub["metrics"], "styleLabels": pub["styleLabels"], "N": len(A["T"]), "priorYear": A.get("priorYear"),
        "played": [{"home": str(e["home"]["id"]), "away": str(e["away"]["id"]), "hs": e["hs"], "as": e["as"], "start": e["start"],
                    "round": e.get("round")} for e in (d.get("played") or []) if e.get("hs") is not None],
        "live": [{"home": str(e["home"]["id"]), "away": str(e["away"]["id"]), "hs": e.get("hs"), "as": e.get("as"),
                  "clock": e.get("clock") or e.get("statusText")} for e in d.get("live") or []],
        "results": [{"home": str(e["home"]["id"]), "away": str(e["away"]["id"]), "hs": e["hs"], "as": e["as"],
                     "start": e["start"], "round": e.get("round")} for e in (d.get("played") or [])[:10]],
        "fanta": fanta, "fantaRules": fv.get("rules"),
        "history": {"summary": model.history_summary(HISTORY),
                    "items": [{"home": str(it["home"]["id"]), "away": str(it["away"]["id"]), "start": it["start"],
                               "pick": (it.get("final") or it.get("latest") or {}).get("pick"), "result": it.get("result"),
                               "ok": (it.get("eval") or {}).get("pick")} for it in hist]},
    }


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
    return web.json_response({**STATE["data"], "analysis": an["pub"], "fixtures": an["fixtures"], "extras": extras,
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
    return web.json_response(model.predict(A, e["home"]["id"], e["away"]["id"], e, MATCHES.get(str(e["id"]))))


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
    if kind == "player":
        eid = (REG["info"].get(iid) or {}).get("espnId")
        return f"https://a.espncdn.com/i/headshots/soccer/players/full/{eid}.png" if eid else None
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


async def h_favicon(_):
    """Icona della scheda del browser: il pallone dell'app, ritagliato perché si veda anche piccolo."""
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
    app.router.add_get("/favicon.ico", h_favicon)
    app.router.add_get("/api/data", h_data)
    app.router.add_get("/api/match/{id}", h_match)
    app.router.add_get("/api/predict", h_predict)
    app.router.add_get("/api/history", h_history)
    app.router.add_get("/api/fanta", h_fanta)
    app.router.add_get("/api/snapshot", h_snapshot)
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
    if DATA_FILE.exists():
        STATE["data"] = load_json(DATA_FILE, None)
        if STATE["data"]:
            reg_seed(STATE["data"])
            refresh_squads(STATE["data"])
            STATUS["statsAt"] = STATE["data"].get("fullAt")
            log("Caricati gli ultimi dati salvati")
    print(f"Serie A Live pronto su {url}  (chiudi questa finestra o premi Ctrl+C per fermarlo)", flush=True)
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
            sys.exit(asyncio.run(cloud_main()))
        asyncio.run(main())
    except KeyboardInterrupt:
        pass
