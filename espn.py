"""ESPN: calendario, classifica, tabellini, formazioni e quote; anagrafica dei giocatori (REG).
Pezzo di server.py (diviso il 13/11/2026): i nomi restano raggiungibili come server.<nome>. Importare sempre
server, mai questo file da solo. save_json si chiama come server.save_json: le prove lo sostituiscono."""
import server
from server import (
    CUP, DATA_FILE, ESPNMAP, ESPN_FILE, ESPN_SITE, ESPN_STAND, EXTRA, HTTP, LEGA, LEGA_KEY, LINEUP_EVERY, MATCHES,
    MATCH_FILE, MATCH_LENGTH, PRIOR, PRIOR_FILE, REG, ZONE_RULES, aiohttp, datetime, difflib, errtxt, fonti,
    letture, log, match_entry, model, prior_ref_pending, prior_ref_step, re, statistiche, time, timezone,
    unicodedata)


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
                  "STATUS_ABANDONED": ("postponed", "Sospesa", 70), "STATUS_SUSPENDED": ("postponed", "Sospesa", 70)}
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
    # finita ma non conclusa (sospesa o interrotta con un nome che la tabella non ha): non è una partita giocata, se no
    # il punteggio del momento entra in classifica, minuti e statistiche (Rayo-Athletic della Liga, 08/11/2026)
    if state == "finished" and typ.get("completed") is False:
        state, text, code = "postponed", "Sospesa", 70
    score =lambda x: int(x["score"]) if state in ("inprogress", "finished") and str(x.get("score", "")).isdigit() else None
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
        # rinviate e sospese già passate: il loro mese si riscarica finché ESPN non dà il risultato o la data nuova
        # (Cambuur-Go Ahead Eagles dell'Eredivisie, sospesa il 31/10 e poi finita, restava «Suspended»)
        sosp = EXTRA.setdefault("sospese", {})
        if ev["status"] == "postponed" and ev["start"] < time.time():
            sosp[x["espn"]] = ev["start"]
        else:
            sosp.pop(x["espn"], None)
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
                   or (x.get("ev") or {}).get("v") != letture.EV_VERSION   # cronaca letta con una versione vecchia
                   # cronaca vuota letta prima della cronaca ridotta dagli eventi chiave (Süper Lig, 08/11/2026)
                   or ("ev" in x and not (x["ev"] or {}).get("ev") and (x["ev"] or {}).get("kv") != 1))
        # l'arbitro a volte ESPN lo aggiunge giorni dopo (in Premier): si riprova ogni 6 ore per tre giorni
        noref = not (x.get("referee") or {}).get("name") and now - e["start"] < 3 * 86400
        # la cronaca scaricata appena finita la partita può non avere ancora l'ultimo gol (Villarreal-Getafe 2-0 della
        # Liga: il gol al 90'+1' mancava): per tre giorni si riscarica ogni ora finché i gol non tornano col risultato
        evs = (x.get("ev") or {}).get("ev") or []
        short = ("ev" in x and e.get("hs") is not None and now - e["start"] < 3 * 86400
                 and sum(1 for g in evs if g.get("k") in ("goal", "og")) < e["hs"] + e["as"])
        wait = 120 if missing else 3600 if not x.get("final") or short else 6 * 3600
        if e.get("espn") and (not x.get("final") or missing or noref or short) and now - x.get("espnAt", 0) >= wait:
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
    if LEGA["dir"]:
        return number_rounds_auto(d, evs)
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


def number_rounds_auto(d, evs):
    """Giornate delle leghe che non le hanno da nessuna fonte (tutte tranne la Serie A, che le ha da Fantacalcio.it; ESPN
    non le dà nemmeno nell'API core). Le partite giocate o in corso tengono la loro, perché storico e letture la
    usano già; le altre si rifanno a ogni giro in ordine di data: una giornata finisce quando una squadra gioca di nuovo
    o quando ha già tutte le partite. Una giornata in mezzo al calendario con meno di metà delle partite è un gruppo di
    recuperi (Liga, 02/12/2026: Real Sociedad-Real Madrid e Barcelona-Atlético, prima della giornata del 06/12):
    quelle partite restano senza giornata, con «recupero», invece di finire nella giornata dopo con le squadre due
    volte. Revisione dell'08/11/2026."""
    per = max(1, len(d.get("teams") or {}) // 2)
    teams_in, size, cur, auto = {}, {}, 0, []
    for e in evs:
        h, a = e["home"]["id"], e["away"]["id"]
        if e.get("status") in ("finished", "inprogress") and (e.get("round") or e.get("recupero")):
            if e.get("round"):
                cur = max(cur, e["round"])
                teams_in.setdefault(e["round"], set()).update((h, a))
                size[e["round"]] = size.get(e["round"], 0) + 1
            continue
        e.pop("recupero", None)
        r = cur or 1
        if h in teams_in.get(r, ()) or a in teams_in.get(r, ()) or size.get(r, 0) >= per:
            r = cur + 1
        e["round"] = r
        auto.append(e)
        cur = r
        teams_in.setdefault(r, set()).update((h, a))
        size[r] = size.get(r, 0) + 1
    ids = {id(e) for e in auto}
    fixed = {e["round"] for e in evs if id(e) not in ids and e.get("round")}
    rec = sorted(r for r in {e["round"] for e in auto}
                 if r not in fixed and r > max(fixed or {0}) and r != cur and size[r] < per / 2)
    for r in rec:   # le partite del gruppo piccolo che stanno nella giornata dopo ci vanno; le altre sono recuperi
        for e in [e for e in auto if e["round"] == r]:
            h, a = e["home"]["id"], e["away"]["id"]
            if h not in teams_in[r + 1] and a not in teams_in[r + 1] and size[r + 1] < per:
                e["round"] = r + 1
                teams_in[r + 1].update((h, a))
                size[r + 1] += 1
            else:
                e["round"], e["recupero"] = None, True
    for e in auto:
        if e["round"]:
            e["round"] -= sum(1 for q in rec if q < e["round"])


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
    server.save_json(MATCH_FILE, MATCHES)
    server.save_json(ESPN_FILE, ESPNMAP)
    server.save_json(DATA_FILE, d)
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
        server.save_json(PRIOR_FILE, PRIOR)
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
    server.save_json(PRIOR_FILE, PRIOR)


def in_window(d, now):
    if d.get("live"):
        return True
    return any(e.get("status") == "notstarted" and e["start"] - 300 <= now <= e["start"] + MATCH_LENGTH
               for e in d.get("next", []))


def next_kickoff(d, now):
    starts = [e["start"] - 300 for e in d.get("next", []) if e.get("status") == "notstarted" and e["start"] - 300 > now]
    return min(starts) if starts else None
