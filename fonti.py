"""Fonti per i dati di ogni partita e per gli allenatori.

- fantacalcio.it: probabili formazioni con le percentuali, squalificati, diffidati, infortunati, in dubbio; arbitro
  designato (2-3 giorni prima, mentre ESPN lo mette solo il giorno della partita)
- Wikipedia: allenatori della stagione (e di quella scorsa, per sapere chi è nuovo); in inglese i cambi di
  allenatore con le date, spesso aggiornati prima (Fantacalcio.it, Lega Serie A ed ESPN arrivano dopo o non li hanno)
- ESPN: precedenti tra le squadre, arbitro designato e cartellini delle partite (per le statistiche degli arbitri)

Qui ci sono solo le funzioni che leggono le pagine: le richieste le fa server.py.
"""
import html
import json
import re
import unicodedata
from datetime import datetime, timezone

FC_PROBABILI = "https://www.fantacalcio.it/probabili-formazioni-serie-a"
FC_CALENDARIO = "https://www.fantacalcio.it/serie-a/calendario/{giornata}"   # con i link alle pagine delle partite
# pagina di una partita: conta l'id, e la giornata deve essere giusta; il nome delle squadre nell'indirizzo no
FC_PARTITA = "https://www.fantacalcio.it/serie-a/calendario/{giornata}/{stagione}/casa-ospite/{id}"
WIKI = "https://it.wikipedia.org/wiki/Serie_A_{a}-{b}"
WIKI_EN = "https://en.wikipedia.org/w/api.php"
WIKI_EN_TITLE = "{a}–{b:02d} Serie A"   # "2026–27 Serie A"
COME = {"sacked": "esonero", "mutual consent": "risoluzione consensuale", "resigned": "dimissioni",
        "end of contract": "fine del contratto", "end of caretaker": "fine dell'interim", "retired": "ritiro",
        "signed by": "passato a un'altra squadra", "health": "motivi di salute"}
MESI_EN = {m: i for i, m in enumerate(("january", "february", "march", "april", "may", "june", "july", "august",
                                       "september", "october", "november", "december"), 1)}


def _text(s):
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", s or ""))).strip()


# ---------- fantacalcio.it ----------

def parse_calendario_fc(page):
    """Pagina di una giornata su fantacalcio.it -> [("casa-ospite", indirizzo della pagina della partita)]."""
    out = {}
    for m in re.finditer(r'href="(?:https://www\.fantacalcio\.it)?(/serie-a/calendario/\d+/[\d-]+/([a-z0-9-]+)/\d+)"', page):
        out.setdefault(m.group(2), "https://www.fantacalcio.it" + m.group(1))
    return list(out.items())


def parse_arbitro_fc(page):
    """Pagina di una partita su fantacalcio.it -> cognome dell'arbitro designato, se c'è già."""
    m = re.search(r'<div class="referee">(.*?)</div>', page, re.S)
    name = _text(m.group(1)) if m else ""
    return name or None


def parse_partita_fc(page):
    """Pagina di una partita su fantacalcio.it -> (casa, ospite, cognome dell'arbitro); None se la partita non c'è
    (fantacalcio.it risponde comunque, con una pagina «404 pagina non trovata»)."""
    m = re.search(r"<title>\s*Riepilogo match ([^<-]+?)-([^<-]+?) \d+ giornata", page)
    return (m.group(1).strip(), m.group(2).strip(), parse_arbitro_fc(page)) if m else None


def parse_id_partita_fc(page, giornata, stagione):
    """Pagina di una giornata passata su fantacalcio.it: mostra una sola partita -> il suo id (le altre 9 della
    giornata hanno gli id vicini)."""
    m = re.search(rf"/serie-a/calendario/{giornata}/{stagione}/[a-z0-9-]+/(\d+)", page)
    return int(m.group(1)) if m else None


def _pills(block):
    out = []
    for li in re.findall(r'<li class="player-item[^"]*"[^>]*>(.*?)</li>', block, re.S):
        name = re.search(r'<a class="player-name[^>]*>\s*<span>(.*?)</span>', li, re.S)
        if not name:
            continue
        role = re.search(r'class="role" data-value="(\w)"', li)
        pct = re.search(r'aria-valuenow="(\d+)"', li)
        out.append({"name": _text(name.group(1)), "role": role.group(1) if role else None,
                    "pct": int(pct.group(1)) if pct else None})
    return out


def _names(part):
    """Giocatori di un riquadro (squalificati, infortunati...), con la descrizione se c'è."""
    out = []
    for m in re.finditer(r'<a class="player-name[^>]*>\s*<span>(.*?)</span>\s*</a>\s*(?:<p class="description">(.*?)</p>)?',
                         part, re.S):
        out.append({"name": _text(m.group(1)), "desc": _text(m.group(2)) or None})
    return out


def _section(seg, cls):
    m = re.search(r'<section class="%s">(.*?)</section>' % cls, seg, re.S)
    if not m:
        return [[], []]
    parts = m.group(1).split('<div class="content">')[1:]
    res = [_names(p) for p in parts[:2]]
    return res + [[]] * (2 - len(res))


def parse_probabili(page):
    """Pagina delle probabili formazioni -> una voce per partita, con le due squadre in ordine casa/trasferta."""
    matches = []
    for seg in page.split('class="match-info"')[1:]:
        cards = seg.split('class="card team-card')[1:3]
        if len(cards) < 2:
            continue
        date = re.search(r'class="match-date">(.*?)<', seg)
        upd = re.search(r'Ultimo aggiornamento <span class="date">(.*?)</span>', seg)
        extra = {k: _section(seg, cls) for k, cls in (("suspended", "suspendeds"), ("cautioned", "cautioneds"),
                                                      ("injured", "injureds"), ("doubtful", "dubts"))}
        sides = []
        for i, c in enumerate(cards):
            team = re.search(r'class="h6 team-name">(.*?)<', c)
            form = re.search(r'class="h6 team-formation">(.*?)<', c)
            st = c.split('class="player-list starters"')[1] if 'class="player-list starters"' in c else ""
            st, _, bench = st.partition('class="player-list reserves"')
            side = {"team": _text(team.group(1)) if team else "", "formation": _text(form.group(1)) if form else None,
                    "starters": _pills(st), "bench": _pills(bench)}
            side.update({k: v[i] for k, v in extra.items()})
            sides.append(side)
        if all(s["team"] for s in sides) and all(len(s["starters"]) == 11 for s in sides):
            matches.append({"date": _text(date.group(1)) if date else None,
                            "updated": _text(upd.group(1)) if upd else None, "home": sides[0], "away": sides[1]})
    return matches


def lines_positions(formation, starters):
    """Ruolo in campo (G/D/M/F) di ogni titolare: portiere, poi le linee del modulo dalla difesa all'attacco.
    Nella pagina i titolari sono in quest'ordine, ogni linea da destra a sinistra (come le formazioni ufficiali)."""
    try:
        lines = [int(x) for x in (formation or "").split("-")]
    except ValueError:
        lines = []
    if sum(lines) != 10 or len(starters) != 11:
        by_role = {"p": "G", "d": "D", "c": "M", "a": "F"}
        return [by_role.get(p.get("role"), "M") for p in starters], False
    pos = ["G"]
    for i, n in enumerate(lines):
        pos += ["D" if i == 0 else "F" if i == len(lines) - 1 else "M"] * n
    return pos, True


# ---------- Wikipedia ----------

def parse_allenatori(page):
    """Tabella 'Allenatori e primatisti' -> {squadra: [{"name", "from", "to"}]}: gli allenatori della stagione
    in ordine, con le giornate in cui sono stati in panchina (to = None se è ancora lì)."""
    for t in re.findall(r'<table class="wikitable.*?</table>', page, re.S):
        rows = re.findall(r"<tr.*?</tr>", t, re.S)
        cells = lambda r: [_text(c) for c in re.findall(r"<t[hd][^>]*>(.*?)</t[hd]>", r, re.S)]
        head = cells(rows[0]) if rows else []
        if "Allenatore" in head and "Squadra" in head:
            ci, ti = head.index("Allenatore"), head.index("Squadra")
            out = {}
            for r in rows[1:]:
                c = [re.sub(r"\[[^\]]*\]", "", x).strip() for x in cells(r)]
                if len(c) > max(ci, ti) and c[ti] and c[ci]:
                    out[c[ti]] = parse_tenures(c[ci])
            return out
    return {}


def parse_tenures(cell):
    """"Igor Tudor (1ª-8ª) Massimo Brambilla (9ª) Luciano Spalletti (10ª-)" -> allenatori con le giornate."""
    out = []
    for m in re.finditer(r"([^()]+?)\s*(?:\(([^)]*)\)|$)", cell):
        name = re.sub(r"^[,/\s]+|[,/\s]+$", "", m.group(1))
        if not name:
            continue
        rng = m.group(2) or ""
        nums = [int(n) for n in re.findall(r"\d+", rng)]
        fr = nums[0] if nums else None
        to = nums[1] if len(nums) > 1 else (None if "-" in rng or not nums else nums[0])
        out.append({"name": name, "from": fr, "to": to})
    if out:
        out[-1]["to"] = out[-1]["to"] if len(out) > 1 or out[-1]["from"] else None
    return out


def coach_at(tenures, rnd):
    """Allenatore in panchina in una certa giornata (l'ultimo se la giornata non è nota)."""
    if not tenures:
        return None
    if rnd:
        for t in tenures:
            if (t["from"] or 1) <= rnd <= (t["to"] or 99):
                return t["name"]
    return tenures[-1]["name"]


def table_grid(table):
    """Righe di una tabella HTML come liste di testi, ripetendo le celle unite (rowspan e colspan)."""
    grid, carry = [], {}   # carry: colonna -> (testo, righe che restano, viene dall'intestazione)
    for r in re.findall(r"<tr[^>]*>(.*?)</tr>", table, re.S):
        cells = re.findall(r"<t([hd])([^>]*)>(.*?)</t[hd]>", r, re.S)
        if any(c[0] == "d" for c in cells):
            # un'intestazione non scende nelle righe dei dati (nella pagina della Liga 2026/27 «Date of vacancy» ha
            # rowspan=2 per errore e spostava tutte le colonne della prima riga)
            carry = {c: v for c, v in carry.items() if not v[2]}
        row, col, k = [], 0, 0
        while k < len(cells) or col in carry:
            if col in carry:
                text, left, head = carry.pop(col)
                if left > 1:
                    carry[col] = (text, left - 1, head)
            else:
                kind, attrs, body = cells[k]
                k += 1
                text = re.sub(r"\[[^\]]*\]", "", _text(body)).strip()
                wide = re.search(r'colspan="?(\d+)', attrs)
                down = re.search(r'rowspan="?(\d+)', attrs)
                for _ in range(int(wide.group(1)) - 1 if wide else 0):
                    row.append(text)
                    col += 1
                if down and int(down.group(1)) > 1:
                    carry[col] = (text, int(down.group(1)) - 1, kind == "h" and all(c[0] == "h" for c in cells))
            row.append(text)
            col += 1
        grid.append(row)
    return grid


def _data_en(s):
    m = re.search(r"(\d{1,2}) ([A-Za-z]+) (\d{4})", s or "")
    if not m or m.group(2).lower() not in MESI_EN:
        return None
    return int(datetime(int(m.group(3)), MESI_EN[m.group(2).lower()], int(m.group(1)), 12, tzinfo=timezone.utc).timestamp())


def parse_cambi_en(page):
    """Tabella «Managerial changes» di Wikipedia in inglese -> cambi di allenatore della stagione, in ordine:
    [{"team", "out", "how", "left" (data), "in" (None se non è ancora stato nominato), "since" (data)}]."""
    clean = lambda s: re.sub(r"\s*\((?:caretaker|interim)\)", "", s or "", flags=re.I).strip()
    for t in re.findall(r'<table class="wikitable.*?</table>', page, re.S):
        grid = table_grid(t)
        head = [h.lower() for h in grid[0]] if grid else []
        col = lambda key: next((i for i, h in enumerate(head) if key in h), None)
        it, io, ih, il, ii, isn = (col(k) for k in ("team", "outgoing", "manner", "vacancy", "incoming", "appointment"))
        ii = ii if ii is not None else col("replaced")   # in alcune pagine (Serie A) la colonna è «Replaced by»
        ip = col("position")
        if None in (it, io, ii):
            continue
        cell = lambda g, i: g[i] if i is not None and i < len(g) else ""
        out = []
        for g in grid[1:]:
            if not cell(g, it) or not cell(g, io) or cell(g, it).lower() == head[it]:   # riga d'intestazione ripetuta
                continue
            how = cell(g, ih).lower()
            out.append({"team": cell(g, it), "out": clean(cell(g, io)), "how": next((v for k, v in COME.items() if k in how), None),
                        "left": _data_en(cell(g, il)), "in": clean(cell(g, ii)) or None, "since": _data_en(cell(g, isn)),
                        "pre": "pre-season" in cell(g, ip).lower()})   # cambio d'estate, prima del campionato
        return out
    return []


def parse_personale_en(page):
    """Tabella «Personnel and kits» di Wikipedia in inglese (leghe senza la tabella degli allenatori in italiano) ->
    {squadra: [{"name": allenatore}]}, nello stesso formato di parse_allenatori ma senza le giornate."""
    for t in re.findall(r'<table class="wikitable.*?</table>', page, re.S):
        grid = table_grid(t)
        head = [h.lower() for h in grid[0]] if grid else []
        it = next((i for i, h in enumerate(head) if h in ("team", "club")), None)
        im = next((i for i, h in enumerate(head) if "manager" in h or "head coach" in h), None)
        if it is None or im is None:
            continue
        clean = lambda s: re.sub(r"\s*\((?:caretaker|interim)\)", "", s or "", flags=re.I).strip()
        return {g[it]: [{"name": clean(g[im]), "from": None, "to": None}] for g in grid[1:]
                if len(g) > max(it, im) and g[it] and clean(g[im]) and g[it].lower() != head[it]}   # niente riga d'intestazione
    return {}


# ---------- OneFootball (probabili formazioni delle leghe senza Fantacalcio.it) ----------

OF_FIXTURES = "https://onefootball.com/en/competition/{lega}/fixtures"
OF_MATCH = "https://onefootball.com/en/match/{id}"


# ---------- Opta (dal sito Opta Analyst, che pubblica le statistiche Opta della stagione) ----------

OPTA_PAGE = "https://theanalyst.com/competition/{lega}/stats"   # contiene il codice Opta della stagione (tmcl)
OPTA_STATS = "https://theanalyst.com/wp-json/sdapi/v1/soccerdata/tournamentstats?tmcl={tmcl}"
OPTA_GROUPS = (("attack", "overall"), ("possession", "chanceCreation"), ("carries", "overall"), ("defending", "overall"),
               ("defending", "discipline"), ("goalkeeping", "overall"))
OPTA_KEEP = {"mins_played", "apps", "goals", "xg", "shots", "shots_on_target", "xa", "chances_created", "assists", "carries",
             "progressive_carries", "tackles", "interceptions", "recoveries", "blocks", "clearances", "aerial_duels",
             "aerial_duels_won", "ground_duels", "ground_duels_won", "fouls_commited", "yellows", "reds", "saves_made",
             "goals_prevented", "xgot_conceded", "goals_conceded"}


def parse_opta_tmcl(page):
    """Pagina delle statistiche di una lega su Opta Analyst -> codice Opta della stagione in corso."""
    m = re.search(r'"tmcl":"([a-z0-9]+)"', page)
    return m.group(1) if m else None


def parse_opta_players(data):
    """Statistiche Opta della stagione (tournamentstats di Opta Analyst, divise in gruppi: attacco, creazione,
    conduzioni, difesa, disciplina, portieri) -> {id Opta: {"name", "team", campi}} con i gruppi uniti."""
    out = {}
    for g, sub in OPTA_GROUPS:
        for r in (((data.get("player") or {}).get(g) or {}).get(sub) or []):
            pid = str(r.get("player_id") or r.get("player_uuid") or "")
            if not pid:
                continue
            o = out.setdefault(pid, {"name": r.get("player") or f"{r.get('first_name', '')} {r.get('last_name', '')}".strip(),
                                     "team": r.get("contestantName") or r.get("contestantShortName"),
                                     "pos": r.get("squad_position")})
            o.update({k: r[k] for k in OPTA_KEEP if r.get(k) is not None})
    return out


OF_TABLE = "https://onefootball.com/en/competition/{lega}/table"
OF_SQUAD = "https://onefootball.com/en/team/{team}/squad"
OF_PHOTO = "https://images.onefootball.com/players/180/{id}.jpg"


def parse_of_teams(page):
    """Classifica di una lega su OneFootball -> indirizzi delle squadre ("arsenal-2"), anche di altre competizioni
    citate nella pagina: si tengono solo quelle che corrispondono alle squadre della lega."""
    out = []
    for t in re.findall(r'href="/en/team/([a-z0-9-]+-\d+)"', page):
        if t not in out:
            out.append(t)
    return out


def parse_of_squad(page):
    """Rosa di una squadra su OneFootball -> [(nome, id OneFootball)]: la foto è OF_PHOTO con quell'id."""
    out = []
    for name, pid in re.findall(r'"@type":"Person","@id":"[^"]*","name":"([^"]+)","url":"https://onefootball\.com/en/player/[a-z0-9-]+-(\d+)"', page):
        name = html.unescape(json.loads(f'"{name}"') if "\\u" in name else name)
        if (name, pid) not in out:
            out.append((name, pid))
    return out


def parse_of_fixtures(page):
    """Calendario di una lega su OneFootball -> id delle prossime partite, in ordine."""
    out = []
    for m in re.findall(r'href="/en/match/(\d+)"', page):
        if m not in out:
            out.append(m)
    return out


def parse_of_match(page):
    """Pagina di una partita su OneFootball -> {"home", "away", "kind" ("Predicted" o le ufficiali), "lineups":
    {"home"/"away": {"formation", "starters": [{"name"}]}}} o None. OneFootball dà le righe dall'attacco al portiere,
    ognuna da sinistra a destra: qui diventano portiere, poi difesa -> attacco, ogni linea da destra a sinistra (come
    le formazioni ufficiali e quelle di Fantacalcio.it)."""
    import json as _json
    m = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', page, re.S)
    if not m:
        return None
    found = {}

    def walk(x):
        if isinstance(x, dict):
            if x.get("$case") == "matchLineup" and "lu" not in found:
                found["lu"] = x["matchLineup"]
            for k in ("lineup_type",):
                if isinstance(x.get(k), dict) and "kind" not in found:
                    found["kind"] = x[k].get("value")
            for v in x.values():
                walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)
    walk(_json.loads(m.group(1)))
    lu = ((found.get("lu") or {}).get("variant") or {}).get("lineup")
    if not lu:
        return None
    out = {"kind": found.get("kind") or "", "title": (found.get("lu") or {}).get("title"), "lineups": {}}
    for side, key in (("home", "homeTeam"), ("away", "awayTeam")):
        tm = lu.get(key) or {}
        rows = (((tm.get("variant") or {}).get("formation") or {}).get("rows")) or []
        rows = [[p.get("name") for p in r.get("players") or [] if p.get("name")] for r in rows]
        if sum(len(r) for r in rows) != 11:
            return None
        rows = rows[::-1]   # portiere, difesa, ..., attacco
        out[side] = tm.get("teamName")
        out["lineups"][side] = {"formation": "-".join(str(len(r)) for r in rows[1:]),
                                "starters": [{"name": n} for r in rows for n in r[::-1]]}
    return out


def stesso(a, b):
    """Stessa persona: nomi uguali senza accenti, oppure stesso cognome."""
    n = lambda s: re.sub(r"[^a-z ]", "", unicodedata.normalize("NFKD", s or "").encode("ascii", "ignore").decode().lower()).split()
    x, y = n(a), n(b)
    return bool(x and y and (x == y or x[-1] == y[-1]))


def allenatore_attuale(ten, cambi):
    """Chi allena adesso: Wikipedia in italiano (giornate in panchina) e in inglese (cambi con le date); vince
    la fonte che conosce il cambio più recente. -> (nome, lasciato): nome è None se la panchina è vuota, e
    lasciato dice chi è andato via, dopo quale giornata, quando e come."""
    r = cambi[-1] if cambi else None
    if ten:
        name, closed = ten[-1]["name"], bool(ten[-1].get("to"))
        if r and stesso(r["out"], name) and not (r["in"] and stesso(r["in"], name)):
            name, closed = (r["in"], False) if r["in"] else (name, True)   # l'inglese sa già dell'addio o del successore
    elif r:
        name, closed = (r["in"], False) if r["in"] else (r["out"], True)
    else:
        return None, None
    if not closed:
        return name, None
    after = ten[-1]["to"] if ten and stesso(ten[-1]["name"], name) else None
    info = next((c for c in reversed(cambi or []) if stesso(c["out"], name)), {})
    return None, {"name": name, "after": after, "date": info.get("left"), "how": info.get("how")}


# ---------- ESPN ----------

def espn_h2h(summary):
    """Ultimi precedenti dal riepilogo ESPN: [(id ESPN di casa, id ESPN in trasferta, gol casa, gol trasferta)]."""
    out = []
    for s in summary.get("seasonseries") or []:
        if s.get("type") != "head-to-head":
            continue
        for e in s.get("events") or []:
            if not (e.get("statusType") or {}).get("completed"):
                continue
            c = {x.get("homeAway"): x for x in e.get("competitors") or []}
            try:
                out.append((str(c["home"]["team"]["id"]), str(c["away"]["team"]["id"]),
                            int(c["home"]["score"]), int(c["away"]["score"])))
            except (KeyError, TypeError, ValueError):
                continue
    return out


def espn_referee(summary):
    for o in (summary.get("gameInfo") or {}).get("officials") or []:
        if ((o.get("position") or {}).get("name") or "").lower() == "referee" and o.get("fullName"):
            return o["fullName"]
    return None


def espn_cards(summary):
    """Cartellini gialli e rossi della partita (somma delle due squadre), se la partita è finita."""
    y = r = 0
    teams = (summary.get("boxscore") or {}).get("teams") or []
    if len(teams) != 2:
        return None
    for t in teams:
        st = {s.get("name"): s.get("displayValue") for s in t.get("statistics") or []}
        if st.get("yellowCards") is None:
            return None
        y += int(float(st.get("yellowCards") or 0))
        r += int(float(st.get("redCards") or 0))
    return {"y": y, "r": r}


def espn_goals(summary):
    """Gol della partita: squadra ESPN, marcatore e assist (id ESPN). Gli autogol sono segnati a parte."""
    out = []
    for k in summary.get("keyEvents") or []:
        if not k.get("scoringPlay"):
            continue
        typ = ((k.get("type") or {}).get("text") or "").lower()
        ps = [str((p.get("athlete") or {}).get("id")) for p in k.get("participants") or [] if (p.get("athlete") or {}).get("id")]
        out.append({"team": str((k.get("team") or {}).get("id")), "g": ps[0] if ps else None,
                    "a": ps[1] if len(ps) > 1 and "own" not in typ else None,
                    "og": "own" in typ, "pen": "penalty" in typ})
    return out


def espn_subs(summary):
    """Sostituzioni in ordine: (squadra ESPN, id entrato, id uscito)."""
    out = []
    for k in summary.get("keyEvents") or []:
        if ((k.get("type") or {}).get("type") or "") != "substitution":
            continue
        ps = [str((p.get("athlete") or {}).get("id")) for p in k.get("participants") or []]
        if len(ps) >= 2:
            out.append((str((k.get("team") or {}).get("id")), ps[0], ps[1]))
    return out


def _dec_frac(v):
    """Quota frazionaria ("31/10") o decimale ("4.1") -> decimale."""
    try:
        s = str(v).strip()
        if "/" in s:
            a, b = s.split("/")
            return 1 + float(a) / float(b)
        return float(s)
    except (ValueError, ZeroDivisionError):
        return None


def _dec_us(ml):
    """Quota americana (+130, -200) -> decimale."""
    try:
        ml = float(ml)
    except (TypeError, ValueError):
        return None
    if ml >= 100:
        return 1 + ml / 100
    if ml <= -100:
        return 1 + 100 / -ml
    return None


# bookmaker in ordine di preferenza: le loro quote nei riepiloghi ESPN sono quelle di prima della partita. Unibet e
# Betfair no: sulle partite 2023-2026 dei cinque campionati maggiori «indovinano» troppo (log loss 0,76 e 0,80 contro
# 0,92-0,99 degli altri), cioè sono quote aggiornate durante la partita
ODDS_BOOKS = ["bet 365", "bet365", "draftkings", "espn bet", "titanbets", "sugarhouse", "draftkings (old)"]


def espn_odds(summary):
    """Quote 1X2 di prima della partita nel riepilogo ESPN -> probabilità senza il margine del bookmaker:
    {"p1", "px", "p2", "book", "src"} (book = somma delle probabilità implicite, il margine), o None.
    Bet365 ha le quote «preMatch» frazionarie; DraftKings ed ESPN BET le americane di chiusura. Le «Live Odds» sono
    quelle durante la partita e non si usano (dopo il fischio d'inizio sanno già come sta andando)."""
    best = None
    for o in summary.get("odds") or summary.get("pickcenter") or []:
        name = ((o.get("provider") or {}).get("name") or "").strip()
        if "live" in name.lower() or name.lower() not in ODDS_BOOKS:
            continue
        tm = ((o.get("bettingOdds") or {}).get("teamOdds")) or {}
        d = None
        if tm.get("preMatchFullTimeResultHome"):
            d = [_dec_frac((tm.get(f"preMatchFullTimeResult{k}") or {}).get("value")) for k in ("Home", "Draw", "Away")]
        elif (o.get("homeTeamOdds") or {}).get("moneyLine") is not None:
            d = [_dec_us((o.get(k) or {}).get("moneyLine")) for k in ("homeTeamOdds", "drawOdds", "awayTeamOdds")]
        if not d or any(x is None or x <= 1 for x in d):
            continue
        inv = [1 / x for x in d]
        book = sum(inv)
        if not 1.0 <= book <= 1.25:   # quote strane (sospese, sbagliate): meglio niente
            continue
        cand = {"p1": inv[0] / book, "px": inv[1] / book, "p2": inv[2] / book, "book": round(book, 4), "src": name}
        if best is None or ODDS_BOOKS.index(name.lower()) < ODDS_BOOKS.index(best["src"].lower()):
            best = cand
    return best


def parse_marcatori_en(page):
    """Tabella «Top goalscorers» di una stagione su Wikipedia in inglese -> [[giocatore, squadra, gol]]. Le righe
    riassuntive («Twelve players») si saltano."""
    tab = re.search(r"<table.*?</table>", page or "", re.S)
    out = []
    for row in table_grid(tab.group(0)) if tab else []:
        if len(row) < 4 or not row[-1].strip().isdigit() and not (len(row) >= 5 and row[3].strip().isdigit()):
            continue
        goals = row[3] if len(row) >= 5 and row[3].strip().isdigit() else row[-1]
        name, club = row[1].strip(), row[2].strip()
        if not goals.strip().isdigit() or name.lower().endswith("players") or not name:
            continue
        out.append([name, club, int(goals)])
    return out
