"""Letture delle partite giocate: come sono nati i gol, come hanno giocato le squadre e perché il pronostico è andato
com'è andato.

Fonti: la cronaca di ESPN (è quella di Opta: per ogni gol e tiro dice di piede o di testa, da dove, dove è finito,
l'assist e se è nato da cross, filtrante, calcio d'angolo, punizione o contropiede; poi rigori, pali, espulsioni,
cambi per infortunio e decisioni del VAR), gli xG di ogni tiro di Understat (con la situazione e l'ultima azione prima
del tiro: palla recuperata, ribattuta, dribbling...), possesso e statistiche di squadra di ESPN, pressing (PPDA) di
Understat. Le frasi nascono solo da regole e da questi numeri: niente è inventato.

Qui ci sono solo funzioni pure: le richieste le fa server.py.
"""
import re
import unicodedata

# ---------- cronaca ESPN (Opta) ----------

EV_VERSION = 2   # 2: frasi del VAR in fondo ai gol tolte prima di leggere l'assist (le partite vecchie si rileggono)

ZONE = [("very close range", "a due passi dalla porta", "vicino"), ("six yard box", "dall'area piccola", "vicino"),
        ("more than 35 yards", "da oltre 30 metri", "fuori"), ("long range", "dalla distanza", "fuori"),
        ("outside the box", "da fuori area", "fuori"), ("difficult angle", "da posizione defilata", "lato"),
        ("centre of the box", "dal centro dell'area", "area"), ("right side of the box", "dal lato destro dell'area", "lato"),
        ("left side of the box", "dal lato sinistro dell'area", "lato")]
PLACE = [("top left corner", "all'incrocio", "angolo"), ("top right corner", "all'incrocio", "angolo"),
         ("bottom left corner", "nell'angolo basso", "angolo"), ("bottom right corner", "nell'angolo basso", "angolo"),
         ("high centre", "centrale, sotto la traversa", "centro"), ("centre of the goal", "centrale", "centro")]
BODY = [("right footed", "destro"), ("left footed", "sinistro"), ("header", "colpo di testa")]
# xG approssimati dalla sola cronaca, se Understat non ha ancora la partita
EST_XG = {"vicino": .38, "area": .13, "lato": .06, "fuori": .03}


def _minute(disp):
    """«45'+2'» -> 47.0 (il recupero si somma: serve solo a mettere in fila gli eventi)."""
    n = [int(x) for x in re.findall(r"\d+", disp or "")]
    return float(sum(n[:2])) if n else None


def _norm(s):
    s = unicodedata.normalize("NFKD", str(s or "")).encode("ascii", "ignore").decode().lower()
    return re.sub(r"[^a-z ]+", " ", s).split()


# squadre «femminili» (la Roma, l'Inter, l'Udinese...): per articoli e accordi
FEM = {"fiorentina", "roma", "lazio", "juventus", "atalanta", "sampdoria", "salernitana", "cremonese", "reggiana", "inter",
       "udinese", "spal", "ternana", "triestina", "carrarese", "virtus", "real sociedad"}
PREP = {"di": ("del", "dello", "dell'", "della"), "a": ("al", "allo", "all'", "alla"), "da": ("dal", "dallo", "dall'", "dalla"),
        "su": ("sul", "sullo", "sull'", "sulla"), "in": ("nel", "nello", "nell'", "nella"), "con": ("con il", "con lo", "con l'", "con la")}


def fem(name):
    w = _norm(name)
    return bool(w) and (w[0] in FEM or " ".join(w) in FEM)


def art(name, prep=""):
    """Nome della squadra con l'articolo giusto: «il Genoa», «l'Inter», «la Roma»; con prep="di": «dell'Inter»."""
    n = str(name or "?")
    v = n[:1].lower() in "aeiouh"
    lo = not v and re.match(r"(?i)(s[^aeiou]|z|gn|ps|x)", n) is not None
    i = 2 if v else 3 if fem(n) else 1 if lo else 0
    w = PREP[prep][i] if prep else ("il", "lo", "l'", "la")[i]
    return w + ("" if w.endswith("'") else " ") + n


def adj(name, m, f):
    """Accordo dell'aggettivo con la squadra: adj("Roma", "sbilanciato", "sbilanciata") -> "sbilanciata"."""
    return f if fem(name) else m


def cap(s):
    return s[:1].upper() + s[1:]


def short(name):
    """Cognome per il racconto: «Kevin De Bruyne» -> «De Bruyne», «Valde» resta «Valde»."""
    w = str(name or "").split()
    return " ".join(w[1:]) if len(w) > 1 else (w[0] if w else "?")


def same_name(a, b):
    """Stesso giocatore con nomi scritti in modo diverso (ESPN e Understat): stesso cognome, o parole in comune."""
    na, nb = _norm(a), _norm(b)
    common = set(na) & set(nb)
    # «Paco Esteban» e «Francisco Esteban Sánchez»: il cognome dell'uno è tra le parole dell'altro
    return bool(common) and (na[-1] == nb[-1] or len(common) >= 2 or min(len(na), len(nb)) == 1
                             or (na[-1] in nb and len(na[-1]) >= 4) or (nb[-1] in na and len(nb[-1]) >= 4))


def _detail(rest):
    """Dalla frase di Opta: piede o testa, zona, dove è finito, tipo di assist e situazione."""
    d = {}
    for k, v in BODY:
        if k in rest:
            d["b"] = v
            break
    for k, v, z in ZONE:
        if k in rest:
            d["z"], d["zt"] = z, v
            break
    for k, v, z in PLACE:
        if k in rest:
            d["pl"], d["plt"] = z, v
            break
    if re.search(r"following VAR [Rr]eview", rest):
        d["var"] = 1
    # le frasi del VAR attaccate in fondo («...with a headed pass.Goal awarded following VAR Review.») vanno tolte
    rest = re.sub(r"\.?\s*(?:Goal|Penalty|Card|Decision)[^.]*(?:VAR|[Rr]eview)[^.]*\.?\s*$", ".", rest).strip()
    m = re.search(r"Assisted by (.+?)(?: with a (cross|through ball|headed pass))?(?: following a (corner|set piece situation|fast break))?\.?$", rest)
    if m:
        d["a"] = m.group(1).strip()
        if m.group(2):
            d["at"] = {"cross": "cross", "through ball": "filtrante", "headed pass": "sponda"}[m.group(2)]
        if m.group(3):
            d["sit"] = {"corner": "corner", "set piece situation": "punizione", "fast break": "contropiede"}[m.group(3)]
    else:
        m = re.search(r"following a (corner|set piece situation|fast break)", rest)
        if m:
            d["sit"] = {"corner": "corner", "set piece situation": "punizione", "fast break": "contropiede"}[m.group(1)]
    if "direct free kick" in rest:
        d["sit"] = "punizione diretta"
    if "converts the penalty" in rest:
        d["sit"] = "rigore"
    if "following VAR Review" in rest or "following VAR review" in rest:
        d["var"] = 1
    return d


def parse_espn(j):
    """Riepilogo ESPN di una partita finita -> eventi compatti della cronaca, in ordine:
    {"t": minuto, "m": "45'+2'", "p": tempo, "s": "home"/"away", "k": tipo, ...}. Tipi: goal, og (autogol: s è la
    squadra del giocatore), shot, wood (palo o traversa), penw (rigore ottenuto), penc (rigore causato), pens (rigore
    sbagliato o parato), red, sub, inj (cambio per infortunio), var."""
    side_of = {}
    for r in j.get("rosters") or []:
        for a in r.get("roster") or []:
            nm = (a.get("athlete") or {}).get("displayName")
            if nm and r.get("homeAway") in ("home", "away"):
                side_of[nm] = r["homeAway"]
    com = [c for c in j.get("commentary") or [] if c.get("text")]
    # le squadre nella cronaca hanno nomi propri («Inter Milan»): si riconoscono dai giocatori
    team_side = {}
    for c in com:
        for p, t in re.findall(r"([A-ZÀ-Ý][^.()]*?) \(([^)]+)\)", c["text"]):
            s = side_of.get(p.strip())
            if s:
                team_side.setdefault(t, {}).setdefault(s, 0)
                team_side[t][s] += 1
    team_side = {t: max(v, key=v.get) for t, v in team_side.items()}
    comp = (((j.get("header") or {}).get("competitions") or [{}])[0].get("competitors") or [])
    for c in comp:   # nomi delle squadre senza giocatori citati (rari): il nome ufficiale
        nm = ((c.get("team") or {}).get("displayName") or "")
        if c.get("homeAway") in ("home", "away"):
            team_side.setdefault(nm, c["homeAway"])

    def tside(t, p=None):
        if p and side_of.get(p):
            return side_of[p]
        if t in team_side:
            return team_side[t]
        for k, v in team_side.items():
            if set(_norm(k)) & set(_norm(t)):
                return v
        return None

    out, period, lines = [], 1, []
    for c in com:
        t = c["text"].strip()
        disp = (c.get("time") or {}).get("displayValue") or ""
        if t.startswith("Second Half begins"):
            period = 2
        e = {"t": _minute(disp), "m": disp, "p": period}
        lines.append(e)   # ogni riga della cronaca, anche quelle che non si salvano (falli, angoli...)
        m = re.match(r"^Goal! .+?\d+, .+?\d+\. (.+?) \(([^)]+)\) (.*)$", t)
        if m:
            e.update(k="goal", s=tside(m.group(2), m.group(1)), w=m.group(1), **_detail(m.group(3)))
            # ribattuta secondo la cronaca: subito prima, senza altro in mezzo, tiri della stessa squadra nello stesso
            # minuto; conta l'ultimo parato, respinto o finito sul palo
            for p in reversed(lines[:-1]):
                if p.get("k") not in ("shot", "wood") or p.get("s") != e["s"] or (e["t"] or 0) - (p.get("t") or 0) > 1:
                    break
                if p["k"] == "wood" or p.get("r") in ("saved", "blocked"):
                    e["rb"] = {"w": p.get("w"), "k": p["k"], "r": p.get("r"), "x": p.get("x"), "gk": p.get("gk")}
                    break
            out.append(e)
            continue
        if re.match(r"^Corner, ", t):
            e["k"] = "corner"
        m = re.match(r"^Own Goal by (.+?), (.+?)\. ", t)
        if m:
            e.update(k="og", s=tside(m.group(2), m.group(1)), w=m.group(1))
            out.append(e)
            continue
        m = re.match(r"^Attempt (saved|missed|blocked)\. (.+?) \(([^)]+)\) (.*)$", t)
        if m:
            d = _detail(m.group(4))
            sv = re.search(r"saved .*? by (.+?) \(", m.group(4))
            e.update(k="shot", r=m.group(1), s=tside(m.group(3), m.group(2)), w=m.group(2), **d)
            if sv:
                e["gk"] = sv.group(1)
            out.append(e)
            continue
        m = re.match(r"^(.+?) \(([^)]+)\) hits the (left post|right post|bar)(.*)$", t)
        if m:
            e.update(k="wood", s=tside(m.group(2), m.group(1)), w=m.group(1), x="traversa" if m.group(3) == "bar" else "palo",
                     **_detail(m.group(4)))
            out.append(e)
            continue
        m = re.match(r"^Penalty conceded by (.+?) \(([^)]+)\) (after a foul|with a hand ball)", t)
        if m:
            e.update(k="penc", s=tside(m.group(2), m.group(1)), w=m.group(1), x="mani" if "hand" in m.group(3) else "fallo")
            out.append(e)
            continue
        m = re.match(r"^Penalty (.+?)\. (.+?) draws a foul in the penalty area", t)
        if m:
            e.update(k="penw", s=tside(m.group(1), m.group(2)), w=m.group(2))
            out.append(e)
            continue
        m = re.match(r"^Penalty (saved|missed)! (?:Bad penalty by )?(.+?) \(([^)]+)\)", t)
        if m:
            e.update(k="pens", s=tside(m.group(3), m.group(2)), w=m.group(2), x="parato" if m.group(1) == "saved" else "sbagliato")
            out.append(e)
            continue
        m = re.match(r"^(.+?) \(([^)]+)\) is shown the (red card|second yellow card)", t)
        if m:
            e.update(k="red", s=tside(m.group(2), m.group(1)), w=m.group(1), x="2y" if "second" in m.group(3) else "r")
            out.append(e)
            continue
        m = re.match(r"^Substitution, (.+?)\. (.+?) replaces (.+?)( because of an injury)?\.$", t)
        if m:
            e.update(k="inj" if m.group(4) else "sub", s=tside(m.group(1), m.group(2)), w=m.group(2), o=m.group(3))
            out.append(e)
            continue
        m = re.match(r"^VAR Decision: (.+?)\.?$", t)
        if m:
            e.update(k="var", x=m.group(1))
            out.append(e)
    # un rigore si trasforma in un «Goal!» con «converts the penalty»: lì la situazione è già «rigore»
    return {"ev": [{k: v for k, v in e.items() if v is not None} for e in out if e.get("k") == "var" or e.get("s")], "v": EV_VERSION}



# ---------- Understat: i tiri della partita ----------

US_LAST = {"Rebound": "ribattuta", "Cross": "cross", "Throughball": "filtrante", "TakeOn": "dribbling",
           "BallRecovery": "recupero", "Interception": "recupero", "Tackle": "recupero", "Dispossessed": "recupero",
           "Error": "recupero", "Chipped": "lancio", "Aerial": "duello aereo", "HeadPass": "sponda", "LayOff": "scarico",
           "Standard": "palla inattiva", "Pass": "passaggio", "BlockedPass": "recupero"}
US_SIT = {"OpenPlay": "azione", "FromCorner": "corner", "SetPiece": "punizione", "DirectFreekick": "punizione diretta",
          "Penalty": "rigore"}


US_VERSION = 2   # 2: con le coordinate dei tiri (mappa dei tiri e zone da cui si tira e si subisce)


def parse_understat(j):
    """Dati di una partita di Understat -> tiri compatti per squadra:
    [minuto, giocatore, xG, esito, situazione, tipo di tiro, ultima azione, assist, X, Y]. X va da 0 a 1 verso la
    porta attaccata (la linea dell'area è a 0,84), Y da 0 a 1 da una linea laterale all'altra."""
    out = {}
    for k, side in (("h", "home"), ("a", "away")):
        out[side] = [[int(float(x.get("minute") or 0)), x.get("player"), round(float(x.get("xG") or 0), 3), x.get("result"),
                      x.get("situation"), x.get("shotType"), x.get("lastAction"), x.get("player_assisted"),
                      round(float(x.get("X") or 0), 3), round(float(x.get("Y") or 0), 3)]
                     for x in (j.get("shots") or {}).get(k) or []]
    return out


ZONES = [("piccola", "Area piccola"), ("centro", "Centro dell'area"), ("lati", "Lati dell'area"), ("fuori", "Fuori area")]


def zone(x, y):
    """Zona di un tiro dalle coordinate di Understat."""
    if x is None or y is None:
        return None
    if x < .835:
        return "fuori"
    if x >= .945 and .36 <= y <= .64:
        return "piccola"
    return "centro" if .30 <= y <= .70 else "lati"


# ---------- numeri e parole ----------

def fx(v, d=2):
    return f"{v:.{d}f}".replace(".", ",")


def other(s):
    return "away" if s == "home" else "home"


def xg_outcome(sh_h, sh_a):
    """Probabilità di 1, X e 2 se la partita si rigiocasse con le stesse occasioni (ogni tiro segna con il suo xG)."""
    def dist(xs):
        p = [1.0]
        for x in xs:
            x = min(max(x, 0.0), .99)
            q = [0.0] * (len(p) + 1)
            for i, v in enumerate(p):
                q[i] += v * (1 - x)
                q[i + 1] += v * x
            p = q
        return p
    a, b = dist(sh_h), dist(sh_a)
    p1 = sum(a[i] * b[j] for i in range(len(a)) for j in range(len(b)) if i > j)
    px = sum(a[i] * b[i] for i in range(min(len(a), len(b))))
    return [p1, px, max(0.0, 1 - p1 - px)]


def shots_of(m):
    """Tiri della partita {home: [(minuto, xG, giocatore, esito, situazione, ultima azione)], away: [...]} e la fonte
    degli xG: Understat, oppure una stima dalla cronaca se Understat non ha ancora la partita."""
    us = m.get("us")
    if us and (us.get("home") or us.get("away")):
        return {s: [(x[0], x[2], x[1], x[3], x[4], x[6], x[8] if len(x) > 9 else None, x[9] if len(x) > 9 else None)
                    for x in us.get(s) or [] if x[3] != "OwnGoal"] for s in ("home", "away")}, "understat"
    out = {"home": [], "away": []}
    res = {"saved": "SavedShot", "missed": "MissedShots", "blocked": "BlockedShot"}
    for e in (m.get("ev") or {}).get("ev") or []:
        if e["k"] in ("goal", "shot", "wood") or e["k"] == "pens":
            if e["k"] == "pens" or e.get("sit") == "rigore":
                x = .76
            else:
                x = EST_XG.get(e.get("z"), .08) * (.6 if e.get("b") == "colpo di testa" and e.get("z") != "vicino" else 1)
                x *= 1.3 if e.get("sit") == "contropiede" else 1
            r = ("Goal" if e["k"] == "goal" else "ShotOnPost" if e["k"] == "wood" else
                 ("SavedShot" if e.get("x") == "parato" else "MissedShots") if e["k"] == "pens" else res.get(e.get("r"), "MissedShots"))
            out[e["s"]].append((e.get("t") or 0, round(x, 3), e.get("w"), r, "Penalty" if x == .76 else "OpenPlay", None, None, None))
    return out, "cronaca"


# ---------- i gol ----------

def mp(prep, m):
    """Preposizione + minuto con l'elisione giusta: mp("al", "8'") -> "all'8'", mp("dal", "53'") -> "dal 53'"."""
    m = str(m or "")
    vowel = m[:1] == "8" or re.match(r"^1{1,2}'", m) is not None   # otto, ottanta..., uno, undici
    return (prep[:-1] + "l'" if vowel else prep + " ") + m


def sca(prep, sc):
    """Articolo per un punteggio: sca("", "1-2") -> "l'1-2", sca("su", "0-1") -> "sullo 0-1", sca("su", "2-0") -> "sul 2-0"."""
    sc = str(sc)
    i = 2 if re.match(r"^(1|8|11)-", sc) else 1 if sc.startswith("0") else 0
    w = PREP[prep][i] if prep else ("il", "lo", "l'")[i]
    return w + ("" if w.endswith("'") else " ") + sc


def plural(n, one, many):
    return f"{n} {one if n == 1 else many}"


def goals_of(m):
    """I gol della partita, ciascuno con come è nato e perché (dal punto di vista di chi lo subisce).
    m: {"ev": cronaca, "us": tiri Understat, "names": {home, away}}."""
    ev = (m.get("ev") or {}).get("ev") or []
    us = m.get("us") or {}
    names = m.get("names") or {}
    used, out, score = set(), [], {"home": 0, "away": 0}
    men = {"home": 11, "away": 11}
    entered = {}
    for i, e in enumerate(ev):
        if e["k"] == "red":
            men[e["s"]] -= 1
        if e["k"] in ("sub", "inj"):
            entered[e.get("w")] = e.get("m")
        if e["k"] not in ("goal", "og"):
            continue
        s = e["s"] if e["k"] == "goal" else other(e["s"])   # chi segna
        conc = other(s)
        score[s] += 1
        g = {"m": e.get("m"), "t": e.get("t"), "s": s, "sc": f"{score['home']}-{score['away']}", "w": e.get("w"),
             "a": e.get("a"), "tags": []}
        # il tiro di Understat che corrisponde (stessa squadra, minuto vicino, meglio se stesso giocatore)
        u = None
        if e["k"] == "goal":
            for k, x in enumerate(us.get(s) or []):
                if (s, k) in used or x[3] != "Goal" or abs(x[0] - (e.get("t") or 0)) > 4:
                    continue
                if same_name(x[1], e.get("w")):
                    u = (k, x)
                    break
                if u is None:
                    u = (k, x)
            if u:
                used.add((s, u[0]))
                u = u[1]
        xg = u[2] if u else None
        last = US_LAST.get(u[6]) if u else None
        usit = US_SIT.get(u[4]) if u else None
        if e["k"] == "og":
            cat = "autogol"
        elif e.get("sit") == "rigore" or usit == "rigore":
            cat = "rigore"
        elif e.get("sit") == "corner" or usit == "corner":
            cat = "corner"
        elif e.get("sit") in ("punizione", "punizione diretta") or usit in ("punizione", "punizione diretta"):
            cat = "punizione"
        elif e.get("sit") == "contropiede":
            cat = "contropiede"
        else:
            cat = "azione"
        g["cat"], g["xg"] = cat, xg
        tags = g["tags"]
        if e.get("b") == "colpo di testa":
            tags.append("testa")
        if e.get("z") == "fuori":
            tags.append("fuori")
        if e.get("at") == "cross" or last == "cross" or (last == "lancio" and e.get("b") == "colpo di testa"):
            tags.append("cross")
        if e.get("at") == "filtrante" or last == "filtrante":
            tags.append("filtrante")
        if last in ("recupero", "dribbling", "sponda"):
            tags.append(last)
        if last == "lancio" and "cross" not in tags:
            tags.append("lancio")
        # ribattuta: lo dice Understat; se Understat non sa l'ultima azione, la cronaca (tiri appena prima, senza assist)
        reb = e.get("rb") if (last is None and not e.get("a")) else None
        if last == "ribattuta" or reb:
            tags.append("ribattuta")
        if xg is not None and cat != "rigore":
            if xg >= .3:
                tags.append("nitida")
            elif xg < .07:
                tags.append("difficile")
        if men[conc] < men[s]:
            tags.append("superiorita")
        elif men[s] < men[conc]:
            tags.append("in10")
        if e.get("w") in entered:
            tags.append("subentrato")
            g["in"] = entered[e.get("w")]
        if e.get("a") and e.get("a") in entered:
            tags.append("assist_subentrato")
            g["ain"] = entered[e.get("a")]
        if (e.get("t") or 0) >= 85:
            tags.append("finale")
        elif (e.get("t") or 99) <= 10:
            tags.append("avvio")
        if cat == "rigore":
            pc = next((p for p in reversed(ev[max(0, i - 8):i]) if p["k"] == "penc"), None)
            pw = next((p for p in reversed(ev[max(0, i - 8):i]) if p["k"] == "penw"), None)
            g["pen"] = {"by": pc.get("w") if pc else None, "how": pc.get("x") if pc else None, "won": pw.get("w") if pw else None,
                        "var": any(p["k"] == "var" and "Penalty" in (p.get("x") or "") for p in ev[max(0, i - 8):i])}
        g["reb"] = e.get("rb") if "ribattuta" in tags else None
        g["d"] = {k: e.get(k) for k in ("b", "z", "zt", "pl", "plt", "at", "sit", "var") if e.get(k)}
        g["lab"], g["why"] = why_goal(g, names.get(s, ""), names.get(conc, ""))
        g["how"] = how_goal(g)
        out.append(g)
    return out


def how_goal(g):
    """Il gesto in breve: «sinistro dal centro dell'area all'incrocio, su cross di Osmajic»."""
    d = g.get("d") or {}
    if g["cat"] == "autogol":
        return f"autogol di {short(g['w'])}"
    if g["cat"] == "rigore":
        return f"rigore di {short(g['w'])}" + (" (" + d["plt"] + ")" if d.get("plt") else "")
    parts = [x for x in (d.get("b"), d.get("zt")) if x]
    s = " ".join(parts) + (", " + d["plt"] if d.get("plt") else "")
    if g.get("a"):
        s += {"cross": f", su cross di {short(g['a'])}", "filtrante": f", su filtrante di {short(g['a'])}",
              "sponda": f", su sponda di testa di {short(g['a'])}"}.get(d.get("at"), f", assist di {short(g['a'])}")
    sit = {"corner": " (da calcio d'angolo)", "punizione": " (da punizione)", "punizione diretta": " (punizione diretta)",
           "contropiede": " (in contropiede)"}.get(d.get("sit"), "")
    return (s.strip(", ") or "gol") + sit


def why_goal(g, sn, cn):
    """Perché è nato il gol, visto da chi lo subisce: un'etichetta e una frase. sn: chi segna, cn: chi subisce.
    Etichette: Errore, Palla inattiva, Transizione, Seconda palla, Difesa superata, Prodezza, Giocata individuale,
    Azione manovrata."""
    t, d, xg, cat = g["tags"], g.get("d") or {}, g.get("xg"), g["cat"]
    who, ast = short(g.get("w")), short(g.get("a")) if g.get("a") else None
    xgs = f" (xG {fx(xg)})" if xg is not None else ""
    if cat == "autogol":
        return "Errore", f"Autogol di {short(g['w'])}: {art(cn)} si fa gol da {adj(cn, 'solo', 'sola')}."
    if cat == "rigore":
        p = g.get("pen") or {}
        by = short(p["by"]) if p.get("by") else None
        how = "un fallo di mano" if p.get("how") == "mani" else "un fallo"
        s = f"Rigore{' assegnato dopo il VAR' if p.get('var') or d.get('var') else ''}" + (f" per {how} di {by}" if by else "") + \
            (f" su {short(p['won'])}" if p.get("won") else "") + ": un intervento in area che regala un'occasione da 0,76 xG."
        return "Errore", s
    if cat == "corner":
        if "ribattuta" in t or ("testa" not in t and not ast):
            return "Palla inattiva", f"Da calcio d'angolo: {art(cn)} non allontana il pallone in area e {who} segna da vicino{xgs}."
        if "testa" in t:
            if (xg or 0) >= .25:
                return "Palla inattiva", f"Calcio d'angolo{' di ' + ast if ast else ''} e colpo di testa di {who}{xgs}: marcatura persa in area sulla palla inattiva."
            return "Palla inattiva", f"Calcio d'angolo{' di ' + ast if ast else ''} e colpo di testa di {who}{xgs}: uno stacco difficile, più bravura sua che errore di marcatura."
        return "Palla inattiva", f"Schema su calcio d'angolo: {ast} serve {who}, che calcia {d.get('zt') or 'in area'}{xgs}."
    if cat == "punizione":
        if d.get("sit") == "punizione diretta":
            return "Palla inattiva", f"Punizione diretta di {who}{xgs}: merito del tiratore."
        if "testa" in t:
            return "Palla inattiva", f"Su punizione{' di ' + ast if ast else ''}, colpo di testa di {who}{xgs}: la difesa {art(cn, 'di')} perde l'uomo sulla palla inattiva."
        return "Palla inattiva", f"Nasce da una punizione: {art(cn)} non legge lo sviluppo e {who} segna{xgs}."
    if cat == "contropiede":
        return "Transizione", f"In contropiede{', lanciato da ' + ast if ast else ''}: {art(cn)} era {adj(cn, 'sbilanciato', 'sbilanciata')} in avanti" + \
            (" alla ricerca del gol" if "finale" in t else "") + f" e {who} arriva al tiro{xgs}" + (" senza opposizione." if (xg or 0) >= .3 else ".")
    if "recupero" in t:
        return "Errore", f"Palla persa {art(cn, 'da')} e riconquistata alta {art(sn, 'da')}: {who} punisce subito{xgs}."
    if "difficile" in t:
        if d.get("pl") == "centro" and d.get("z") == "fuori":
            return "Prodezza", f"Tiro da fuori di {who}{xgs}, centrale: un gol difficile, ma su una conclusione così il portiere {art(cn, 'di')} poteva fare di più."
        pre = {"cross": f"Su cross di {ast}, ", "filtrante": f"Su filtrante di {ast}, "}.get(d.get("at"), "")
        where = f" {d['plt']}" if d.get("plt") == "all'incrocio" else ""
        what = "di testa" if "testa" in t else d.get("zt") or ""
        return "Prodezza", f"{pre}{who} segna {what}{where}{xgs}: una conclusione difficile, più merito suo che errore difensivo."
    if "ribattuta" in t:
        r = g.get("reb") or {}
        if r.get("k") == "wood":
            what = f"dopo il {r.get('x')} di {short(r.get('w'))}"
        elif r.get("r") == "saved":
            what = f"dopo la parata{' di ' + short(r.get('gk')) if r.get('gk') else ''} sul tiro di {short(r.get('w'))}"
        elif r.get("r") == "blocked":
            what = f"dopo il tiro respinto di {short(r.get('w'))}"
        else:
            what = "su un pallone rimasto in area"
        return "Seconda palla", f"Su ribattuta, {what}: la difesa {art(cn, 'di')} resta ferma e {who} arriva prima di tutti{xgs}."
    if "filtrante" in t:
        return "Difesa superata", f"Filtrante{' di ' + ast if ast else ''} alle spalle della linea difensiva: {who} si presenta davanti al portiere{xgs}."
    if "cross" in t:
        if "testa" in t:
            return "Difesa superata", f"Cross{' di ' + ast if ast else ''} e colpo di testa di {who}{xgs}: " + \
                ("in area nessuno lo contrasta." if (xg or 0) >= .25 else "vince il duello aereo in area.")
        return "Difesa superata", f"Cross{' di ' + ast if ast else ''} dalla fascia: {who} calcia {d.get('zt') or 'in area'}{xgs}" + \
            (", troppo libero in mezzo all'area." if (xg or 0) >= .3 else ".")
    if "lancio" in t:
        return "Difesa superata", f"Un lancio{' di ' + ast if ast else ''} scavalca la difesa {art(cn, 'di')}: {who} controlla e segna{xgs}."
    if "fuori" in t:
        return "Prodezza", f"Tiro da fuori di {who}{xgs}" + (f", {d['plt']}" if d.get("plt") else "") + ": più merito del tiratore che errore difensivo."
    if "dribbling" in t:
        return "Giocata individuale", f"{who} salta l'uomo e calcia{xgs}: {art(cn)} non riesce a chiudergli lo spazio."
    if "nitida" in t:
        return "Difesa superata", f"Azione manovrata{' (assist di ' + ast + ')' if ast else ''}: {who} si trova libero in una posizione ottima{xgs}."
    return "Azione manovrata", f"Azione manovrata{' (assist di ' + ast + ')' if ast else ''}: {who} calcia {d.get('zt') or 'in area'}{xgs}."


# ---------- la partita ----------

def _seg_stats(shots, t0, t1):
    """xG e tiri di ciascuna squadra tra il minuto t0 (escluso) e t1 (incluso)."""
    out = {}
    for s in ("home", "away"):
        xs = [x for x in shots[s] if t0 < x[0] <= t1]
        out[s] = (sum(x[1] for x in xs), len(xs))
    return out


def style_of(m, s, shots_ev):
    """Come ha giocato una squadra, in poche parole, dai numeri della partita."""
    box = m.get("box") or {}
    b = box.get(s) or {}
    pp = ((m.get("ppda") or {}).get(s) or {}).get("ppda")
    poss = b.get("possession")
    tags = []
    if poss is not None and poss >= 58:
        tags.append(f"possesso ({round(poss)}%)")
    elif poss is not None and poss <= 42:
        tags.append(f"blocco basso ({round(poss)}% di possesso)" if pp is None or pp >= 13 else f"pressing e ripartenze ({round(poss)}% di possesso)")
    if pp is not None and pp <= 8.5 and not any(t.startswith("pressing") for t in tags):
        tags.append(f"pressing alto (PPDA {fx(pp, 1)})")
    if (b.get("totalCrosses") or 0) >= 25:
        tags.append(f"tanti cross ({int(b['totalCrosses'])}, {int(b.get('accurateCrosses') or 0)} riusciti)")
    tp, lb = b.get("totalPasses") or 0, b.get("totalLongBalls") or 0
    if tp and lb / tp >= .17 and lb >= 45:
        tags.append(f"gioco diretto ({int(lb)} lanci lunghi)")
    fb = shots_ev.get(s, 0)
    if fb >= 2:
        tags.append(f"ripartenze ({fb} tiri in contropiede)")
    return tags


def read_match(m, prof=None):
    """Lettura di una partita finita.
    m: {"names": {home, away}, "hs", "as", "box": {home, away} (ESPN), "ev": cronaca, "us": tiri Understat,
        "ppda": {home: {ppda, deep}, away: ...} (Understat), "f": pronostico al calcio d'inizio (o None),
        "ids": {home: id, away: id}}
    prof: profili di stagione delle squadre (per dire se un gol è un difetto che si ripete)."""
    N = m.get("names") or {}
    hs, as_ = m.get("hs"), m.get("as")
    box = m.get("box") or {}
    shots, src = shots_of(m)
    goals = goals_of(m)
    ev = (m.get("ev") or {}).get("ev") or []
    xg = {s: sum(x[1] for x in shots[s]) for s in ("home", "away")}
    nsh = {s: len(shots[s]) for s in ("home", "away")}
    xgp = xg_outcome([x[1] for x in shots["home"]], [x[1] for x in shots["away"]])
    gl = {"home": hs or 0, "away": as_ or 0}
    reds = [e for e in ev if e["k"] == "red"]
    injs = [e for e in ev if e["k"] == "inj" and (e.get("t") or 99) <= 60]
    woods = [e for e in ev if e["k"] == "wood"]
    pensx = [e for e in ev if e["k"] == "pens"]
    big = {s: [x for x in shots[s] if x[1] >= .3 and x[3] != "Goal" and x[4] != "Penalty"] for s in ("home", "away")}
    fbs = {}
    for e in ev:
        if e["k"] in ("shot", "goal", "wood") and e.get("sit") == "contropiede":
            fbs[e["s"]] = fbs.get(e["s"], 0) + 1
    has_f = bool(m.get("f"))
    game = []

    def nm(s):
        return N.get(s) or s

    red_early = {r["s"]: r for r in reds if (r.get("t") or 99) <= 60}
    # 1. le due strategie, e quale ha funzionato
    st = {s: style_of(m, s, fbs) for s in ("home", "away")}
    if st["home"] or st["away"]:
        parts = [f"{nm(s)} {', '.join(st[s])}" if st[s] else f"{nm(s)} senza un tratto marcato" for s in ("home", "away")]
        s_ = "Strategie: " + "; ".join(parts) + "."
        ph, pa = (box.get("home") or {}).get("possession"), (box.get("away") or {}).get("possession")
        if ph is not None and pa is not None and abs(ph - pa) >= 16:
            top = "home" if ph > pa else "away"
            lo = other(top)
            two = next((g for g in goals if g["s"] == lo and (g["t"] or 99) <= 35
                        and int(g["sc"].split("-")[0 if lo == "home" else 1]) - int(g["sc"].split("-")[1 if lo == "home" else 0]) >= 2), None)
            if two and lo not in red_early:
                s_ += f" Il possesso va letto con il risultato: {art(nm(lo))} era già {sca('su', two['sc'])} {mp('al', two['m'])} e ha lasciato il pallone {art(nm(top), 'a')}."
            elif lo in red_early:
                s_ += f" Il possesso va letto con l'espulsione: {art(nm(lo))} è rimast{adj(nm(lo), 'o', 'a')} in dieci {mp('dal', red_early[lo]['m'])}."
            elif xg[lo] > xg[top] + .2:
                s_ += f" Ha funzionato di più l'approccio {art(nm(lo), 'di')}: meno pallone, ma occasioni migliori ({fx(xg[lo])} xG a {fx(xg[top])})."
            elif xg[top] < 1.0:
                s_ += f" Il possesso {art(nm(top), 'di')} è stato sterile: {fx(xg[top])} xG in {nsh[top]} tiri contro una difesa che ha respinto {int((box.get(lo) or {}).get('clearances') or 0)} palloni."
            elif xg[top] - xg[lo] >= .8:
                s_ += f" Il possesso {art(nm(top), 'di')} si è tradotto in occasioni ({fx(xg[top])} xG a {fx(xg[lo])})."
        game.append(s_)
    # 2. le occasioni
    tag = "xG" if src == "understat" else "xG stimati dalla cronaca"
    game.append(f"Occasioni: {nm('home')} {fx(xg['home'])} {tag} con {nsh['home']} tiri, {nm('away')} {fx(xg['away'])} con {nsh['away']}."
                + (f" Rigiocandola con le stesse occasioni finirebbe 1 nel {round(xgp[0] * 100)}% dei casi, X nel {round(xgp[1] * 100)}%, 2 nel {round(xgp[2] * 100)}%."
                   if src == "understat" else ""))
    # 3. le fasi: tra un gol (o un'espulsione) e il successivo, almeno 20 minuti
    marks = sorted([(g["t"] or 0, "g", g) for g in goals] + [(r.get("t") or 0, "r", r) for r in reds], key=lambda x: x[0])
    sc = {"home": 0, "away": 0}
    for idx, (t0, kind, x) in enumerate(marks):
        t1 = marks[idx + 1][0] if idx + 1 < len(marks) else 95
        if kind == "g":
            sc[x["s"]] += 1
        if t1 - t0 < 20:
            continue
        sg = _seg_stats(shots, t0, t1)
        lead = "home" if sc["home"] > sc["away"] else "away" if sc["away"] > sc["home"] else None
        span = mp("dal", x["m"]) + (" " + mp("al", marks[idx + 1][2].get("m")) if idx + 1 < len(marks) else " alla fine")
        if kind == "r":
            s, o = x["s"], other(x["s"])
            game.append(f"In dieci {span} (espulso {short(x['w'])}{', doppio giallo' if x.get('x') == '2y' else ''}), {art(nm(s))} ha tirato {plural(sg[s][1], 'volta', 'volte')} "
                        f"({fx(sg[s][0])} xG), {art(nm(o))} {sg[o][1]} ({fx(sg[o][0])} xG).")
            continue
        if not lead:
            continue
        o = other(lead)
        score = f"{sc['home']}-{sc['away']}"
        if sg[o][1] >= max(5, 1.8 * sg[lead][1]):
            s_ = f"{cap(sca('su', score))} ({span}) {art(nm(lead))} ha difeso il risultato: {art(nm(o))} ha tirato {sg[o][1]} volte contro {sg[lead][1]}"
            s_ += f", ma per appena {fx(sg[o][0])} xG: molti tiri, poche occasioni vere." if sg[o][0] < .1 * sg[o][1] + .3 else f" ({fx(sg[o][0])} xG contro {fx(sg[lead][0])})."
            game.append(s_)
        elif sg[o][0] - sg[lead][0] >= .6:
            game.append(f"{cap(sca('su', score))} ({span}) è cresciut{adj(nm(o), 'o', 'a')} {art(nm(o))}: {fx(sg[o][0])} xG contro {fx(sg[lead][0])}"
                        + (", ma senza riuscire a segnare." if not any(g["s"] == o and t0 < (g["t"] or 0) <= t1 for g in goals) else "."))
        elif sg[lead][0] - sg[o][0] >= .8:
            game.append(f"{cap(sca('su', score))} ({span}) {art(nm(lead))} ha continuato ad attaccare: {fx(sg[lead][0])} xG contro {fx(sg[o][0])}.")
    # 4. episodi: rigori sbagliati, pali, portieri, cambi, infortuni, espulsioni nel finale
    for e in pensx:
        game.append(f"Rigore {e.get('x')} da {short(e.get('w'))} ({nm(e['s'])}) {mp('al', e.get('m'))}.")
    if woods:
        by = {}
        for w in woods:
            by.setdefault(w["s"], []).append(f"{short(w.get('w'))} {w.get('m')}")
        game.append("Legni: " + "; ".join(f"{nm(s)} {len(v)} ({', '.join(v)})" for s, v in by.items()) + ".")
    for s in ("home", "away"):
        sv = int((box.get(s) or {}).get("saves") or 0)
        if sv >= 5:
            o = other(s)
            miss = f", {plural(len(big[o]), 'occasione nitida fallita', 'occasioni nitide fallite')} {art(nm(o), 'da')}" if big[o] else ""
            if gl[o] - gl[s] >= 2:
                game.append(f"Il portiere {art(nm(s), 'di')} ha evitato un passivo più pesante: {sv} parate{miss}.")
            else:
                game.append(f"Il portiere {art(nm(s), 'di')} è stato decisivo: {sv} parate{miss}.")
    bench = []
    for g in goals:
        if "subentrato" in g["tags"]:
            bench.append(f"{short(g['w'])} (entrato {mp('al', g.get('in'))}) ha segnato {sca('', g['sc'])}")
        if "assist_subentrato" in g["tags"]:
            bench.append(f"{short(g['a'])} (entrato {mp('al', g.get('ain'))}) ha servito {sca('', g['sc'])}")
    if bench:
        game.append("Dalla panchina: " + "; ".join(bench) + ".")
    for e in injs:
        game.append(f"{cap(mp('al', e.get('m')))} {art(nm(e['s']))} ha perso {short(e.get('o'))} per infortunio (dentro {short(e.get('w'))}).")
    for r in reds:
        if (r.get("t") or 0) > 60:
            game.append(f"Espulso {short(r.get('w'))} ({nm(r['s'])}) {mp('al', r.get('m'))}{', per doppio giallo' if r.get('x') == '2y' else ''}.")
    if not has_f:   # senza pronostico la concretezza va qui (altrimenti la spiega il verdetto)
        for s in ("home", "away"):
            if gl[s] - xg[s] >= 1.1:
                game.append(f"{cap(art(nm(s)))} è {adj(nm(s), 'stato cinico', 'stata cinica')}: {gl[s]} gol con {fx(xg[s])} xG.")
            elif xg[s] - gl[s] >= 1.1:
                game.append(f"{cap(art(nm(s)))} ha sprecato: {fx(xg[s])} xG e {gl[s]} gol" + (f", {plural(len(big[s]), 'occasione nitida fallita', 'occasioni nitide fallite')}" if big[s] else "") + ".")
    # 5. lezioni dalla stagione: difetti e armi che si ripetono
    lessons = []
    if prof:
        seen = set()
        for g in goals:
            for side, key, verb in ((other(g["s"]), "ga", "subito"), (g["s"], "gf", "segnato")):
                tid = (m.get("ids") or {}).get(side)
                P = (prof or {}).get(str(tid)) or {}
                grp = "palla inattiva" if g["cat"] in ("corner", "punizione") else g["cat"]
                n = sum(v for k, v in (P.get(key) or {}).items() if ("palla inattiva" if k in ("corner", "punizione") else k) == grp)
                tot = sum((P.get(key) or {}).values())
                if (side, key, grp) in seen or grp == "azione" or n < 3 or tot < 4 or n / tot < .3:
                    continue
                seen.add((side, key, grp))
                what = {"palla inattiva": "da palla inattiva", "rigore": "su rigore", "autogol": "su autogol", "contropiede": "in contropiede"}[grp]
                lessons.append(f"{cap(art(nm(side)))} ha {verb} {n} dei suoi {tot} gol {what}: "
                               + ("è un punto debole che si ripete." if key == "ga" else "è una delle sue armi."))
            if g["lab"] == "Errore":
                tid = (m.get("ids") or {}).get(other(g["s"]))
                P = (prof or {}).get(str(tid)) or {}
                ne = sum((P.get("err") or {}).values())
                if ne >= 3 and (other(g["s"]), "err") not in seen:
                    seen.add((other(g["s"]), "err"))
                    lessons.append(f"{cap(art(nm(other(g['s']))))} è già a {ne} gol subiti per errori individuali in stagione.")
    # il momento migliore di ogni squadra: i 15 minuti con più xG, se sono stati davvero suoi
    for s in ("home", "away"):
        best = max(((a, sum(x[1] for x in shots[s] if a <= x[0] < a + 15), sum(1 for x in shots[s] if a <= x[0] < a + 15),
                     sum(x[1] for x in shots[other(s)] if a <= x[0] < a + 15)) for a in range(0, 81, 5)), key=lambda w: w[1])
        if best[1] >= .7 and best[1] >= 2.5 * best[3] and best[1] >= .35 * max(xg[s], .01):
            game.append(f"Il momento migliore {art(nm(s), 'di')}: tra il {best[0]}' e il {best[0] + 15}' "
                        f"({fx(best[1])} xG in {plural(best[2], 'tiro', 'tiri')}, contro {fx(best[3])} {art(nm(other(s)), 'di')}).")
    lu_text, not_started = lineup_reading(m, nm)
    out = {"v": 2, "title": headline(m, goals, xg, reds, nm), "xg": [round(xg["home"], 2), round(xg["away"], 2)], "src": src,
           "xgp": [round(v, 3) for v in xgp], "shots": [nsh["home"], nsh["away"]],
           # tiri per l'andamento e la mappa: [minuto, 0 casa / 1 ospiti, xG, esito, X, Y, giocatore]
           "sh": sorted([[x[0], i, round(x[1], 2), RES_CODE.get(x[3], "M"), x[6], x[7], short(x[2])]
                         for i, s in enumerate(("home", "away")) for x in shots[s]], key=lambda r: (r[0], r[1])),
           "mk": {"g": [[g["t"] or 0, 0 if g["s"] == "home" else 1, g["sc"], short(g["w"]), g["cat"] == "autogol"] for g in goals],
                  "r": [[r.get("t") or 0, 0 if r["s"] == "home" else 1, short(r.get("w"))] for r in reds]},
           "lu": lu_text, "ref": ref_reading(m, ev, nm),
           "goals": [{k: g.get(k) for k in ("m", "s", "sc", "w", "a", "xg", "cat", "lab", "why", "how", "tags")} for g in goals],
           "game": game, "lessons": lessons}
    if has_f and hs is not None:
        f = m["f"]
        out["verdict"] = verdict(m, xg, xgp, goals, reds, big, nm, shots, not_started)
        out["pred"] = {"p1": f.get("p1"), "px": f.get("px"), "p2": f.get("p2"), "label": (f.get("pick") or {}).get("label"),
                       "lh": f.get("lh"), "la": f.get("la")}
    return out


RES_CODE = {"Goal": "G", "SavedShot": "S", "MissedShots": "M", "BlockedShot": "B", "ShotOnPost": "P"}


def lineup_reading(m, nm):
    """Moduli, assenti e, se c'è il pronostico, i titolari previsti che non sono partiti dall'inizio.
    -> (frasi, {lato: [(nome, prob. di segnare)]})."""
    lu, f = m.get("lu") or {}, m.get("f") or {}
    out, miss_txt, not_started = [], [], {}
    forms = [(s, (lu.get(s) or {}).get("formation")) for s in ("home", "away")]
    if any(fm for _, fm in forms):
        out.append("Moduli: " + ", ".join(f"{nm(s)} {fm}" for s, fm in forms if fm) + ".")
    for s in ("home", "away"):
        # gli assenti che contano: chi ha giocato di più in stagione (min, lo aggiunge server.py), al massimo 4
        ms = sorted((x for x in (lu.get(s) or {}).get("missing") or [] if x.get("type") == "missing" and x.get("name")),
                    key=lambda x: -(x.get("min") or 0))
        ms = [x for x in ms if (x.get("min") or 0) >= 90][:4]
        if ms:
            why = lambda x: "squalificato" if x.get("reason") == 3 or "squalif" in (x.get("desc") or "").lower() else "infortunato"
            miss_txt.append(f"{nm(s)} senza " + ", ".join(f"{short(x['name'])} ({why(x)}, {x['min']}' in stagione)" for x in ms))
    if miss_txt:
        out.append("Assenze pesanti: " + "; ".join(miss_txt) + ".")
    pl = f.get("pl") or {}
    # titolari veri: la formazione ufficiale di ESPN salvata dopo la partita
    starters = {s: [p.get("name") for p in (lu.get(s) or {}).get("starters") or []] if lu.get("confirmed") else [] for s in ("home", "away")}
    if pl and starters["home"] and starters["away"]:
        src = f.get("lineups") or ""
        word = "ufficiale" if src == "ufficiale" else "probabile" if src.startswith("probabile") else "stimata"
        for s in ("home", "away"):
            ns = [(p[1], p[7] or 0) for p in pl.get(s) or [] if p[1] and not any(same_name(p[1], n) for n in starters[s])]
            if ns:
                not_started[s] = ns
        if not_started:
            out.append(f"Il pronostico usava la formazione {word}. Titolari previsti che non sono partiti: "
                       + "; ".join(f"{nm(s)} " + ", ".join(short(n) for n, _ in v) for s, v in not_started.items()) + ".")
        else:
            out.append(f"Il pronostico usava la formazione {word}: i titolari previsti sono partiti tutti dall'inizio.")
    return out, not_started


VAR_IT = [(r"^penalty\b", "rigore assegnato"), (r"^no penalty", "rigore tolto"), (r"^no goal|goal cancelled|goal disallowed", "gol annullato"),
          (r"^goal\b", "gol convalidato"), (r"card upgraded|^red card", "cartellino trasformato in rosso"),
          (r"card downgraded|red card cancelled", "rosso tolto"), (r"decision cancelled", "decisione dell'arbitro annullata")]


def ref_reading(m, ev, nm):
    """Arbitro: severità abituale, cartellini contro quelli attesi, falli, rigori e decisioni del VAR."""
    box, R, f = m.get("box") or {}, m.get("ref") or {}, m.get("f") or {}
    out = []
    b = {s: box.get(s) or {} for s in ("home", "away")}
    y = {s: int(b[s].get("yellowCards") or 0) for s in b}
    fo = {s: int(b[s].get("fouls") or 0) for s in b}
    if R.get("name"):
        s_ = f"Arbitro: {R['name']}"
        if R.get("games") and R.get("base") and R.get("yellow") is not None:
            ypg = R["yellow"] / R["games"]
            d = ypg / R["base"] - 1
            tone = "di solito severo" if d >= .15 else "di solito permissivo" if d <= -.15 else "nella media"
            s_ += f", {tone}: {fx(ypg, 1)} gialli a partita in {R['games']} partite, contro {fx(R['base'], 1)} di media"
        out.append(s_ + ".")
    if b["home"] or b["away"]:
        s_ = f"Cartellini: {plural(y['home'] + y['away'], 'giallo', 'gialli')} ({nm('home')} {y['home']}, {nm('away')} {y['away']})"
        exp = f.get("cards")
        if exp:
            e = sum(exp)
            tot = y["home"] + y["away"]
            s_ += f", contro {fx(e, 1)} attesi" + (": partita più nervosa del previsto" if tot >= e + 2 else
                                                     ": arbitro più largo del previsto" if tot <= e - 2 else "")
        reds = [e for e in ev if e["k"] == "red"]
        s_ += ("; " + ", ".join(f"rosso a {short(e.get('w'))} ({nm(e['s'])}, {e.get('m')}{', doppio giallo' if e.get('x') == '2y' else ''})" for e in reds)) if reds else "; nessuna espulsione"
        out.append(s_ + f". Falli: {fo['home'] + fo['away']} ({nm('home')} {fo['home']}, {nm('away')} {fo['away']}).")
    pens = [e for e in ev if e["k"] == "penw"]
    if pens:
        out.append("Rigori: " + ", ".join(f"uno {art(nm(e['s']), 'a')} {mp('al', e.get('m'))}" for e in pens) + ".")
    elif ev:
        out.append("Nessun rigore.")
    var = []
    for e in ev:
        if e["k"] != "var":
            continue
        t = (e.get("x") or "").strip()
        it = next((v for k, v in VAR_IT if re.search(k, t, re.I)), None)
        var.append(f"{it or 'revisione'} {mp('al', e.get('m'))}" if e.get("m") else (it or "revisione"))
    if var:
        out.append("VAR: " + "; ".join(var) + ".")
    return out


def headline(m, goals, xg, reds, nm):
    hs, as_ = m.get("hs") or 0, m.get("as") or 0
    w = None if hs == as_ else "home" if hs > as_ else "away"
    box = m.get("box") or {}
    if reds and (reds[0].get("t") or 99) <= 70:
        r = reds[0]
        res = "e finisce in parità" if not w else ("e perde" if w != r["s"] else "ma vince lo stesso")
        return f"{nm(r['s'])} in dieci {mp('dal', r.get('m'))} {res}"
    if w:
        l = other(w)
        early = [g for g in goals if g["s"] == w and (g["t"] or 99) <= 20]
        poss_l = (box.get(l) or {}).get("possession") or 0
        if xg[l] - xg[w] >= .7:
            return f"{nm(w)} vince oltre i meriti: più occasioni per {art(nm(l))}"
        if len(early) >= 2:
            return f"{nm(w)} decide tutto in avvio" + (f", {nm(l)} col pallone ma senza occasioni" if poss_l >= 58 and xg[l] < 1 else "")
        if poss_l >= 58 and xg[w] > xg[l]:
            return f"{nm(l)} col pallone, {nm(w)} con le occasioni"
        if xg[w] - xg[l] >= 1.5:
            return f"{nm(w)} domina e vince"
        late = [g for g in goals if g["s"] == w and (g["t"] or 0) >= 80]
        if late and abs(hs - as_) == 1:
            return f"{nm(w)} la vince nel finale"
        return f"{nm(w)} vince una partita combattuta" if abs(xg[w] - xg[l]) < .5 else f"Vittoria meritata {art(nm(w), 'di')}"
    d = xg["home"] - xg["away"]
    if abs(d) >= .8:
        s = "home" if d > 0 else "away"
        return f"{nm(s)} spreca, {art(nm(other(s)))} resiste"
    if hs == 0:
        return "Pareggio senza gol e con poche occasioni" if xg["home"] + xg["away"] < 1.6 else "Pareggio senza gol, ma le occasioni c'erano"
    if abs(d) >= .4:
        s = "home" if d > 0 else "away"
        return f"Pareggio, con {art(nm(s))} un po' più pericolos{adj(nm(s), 'o', 'a')}"
    return "Pareggio giusto"


# ---------- perché il pronostico è andato così ----------

def verdict(m, xg, xgp, goals, reds, big, nm, shots, not_started=None):
    f = m["f"]
    hs, as_ = m["hs"], m["as"]
    out = "1" if hs > as_ else "X" if hs == as_ else "2"
    pick = f["pick"]["k"]
    S = {"1": "home", "2": "away"}
    box = m.get("box") or {}
    gl = {"home": hs, "away": as_}

    def field_of(a, b, thr=.35):
        return "X" if abs(a - b) < thr else "1" if a > b else "2"
    field = field_of(xg["home"], xg["away"])
    lam = {"home": f.get("lh"), "away": f.get("la")}
    why = []   # (peso, frase)
    # un'espulsione presto: conta com'era la partita prima
    red = next((r for r in reds if (r.get("t") or 99) <= 75), None)
    pre_field = None
    if red:
        t = red.get("t") or 0
        pre = _seg_stats(shots, -1, t)
        if t >= 25:
            pre_field = field_of(pre["home"][0], pre["away"][0], .3 * t / 90 + .1)
        why.append((10, f"L'espulsione di {short(red.get('w'))} {mp('al', red.get('m'))} ha cambiato la partita: {art(nm(red['s']))} ha giocato "
                        f"{max(0, 90 - int(t))} minuti in dieci. Fino a lì le occasioni erano {fx(pre['home'][0])} a {fx(pre['away'][0])} xG."))
    # episodi che hanno cambiato l'esito: senza quel gol (rigore o autogol) l'1X2 sarebbe diverso
    for g in goals:
        if g["cat"] not in ("rigore", "autogol"):
            continue
        h2, a2 = hs - (g["s"] == "home"), as_ - (g["s"] == "away")
        o2 = "1" if h2 > a2 else "X" if h2 == a2 else "2"
        if o2 != out:
            if g["cat"] == "rigore":
                p = (g.get("why") or "")
                why.append((7, f"Il rigore {mp('del', g['m'])} ha deciso il risultato: {p[0].lower() + p[1:] if p else ''}"))
            else:
                why.append((7, f"L'autogol di {short(g['w'])} {mp('al', g['m'])} ha deciso il risultato: un episodio che nessun modello prevede."))
    # produzione: occasioni create contro quelle attese
    for s in ("home", "away"):
        L = lam.get(s)
        if not L or (red and red["s"] == s and (red.get("t") or 99) <= 60):
            continue   # in dieci per un'ora: produrre meno è ovvio
        o = other(s)
        if xg[s] < .6 * L and L - xg[s] >= .5:
            cause = ""
            ppda_o = ((m.get("ppda") or {}).get(o) or {}).get("ppda")
            poss_s = (box.get(s) or {}).get("possession") or 0
            if poss_s >= 58:
                cause = f": tanto possesso ({round(poss_s)}%) ma nessuna via per entrare in area"
            elif ppda_o is not None and ppda_o <= 9:
                cause = f": il pressing alto {art(nm(o), 'di')} non l'ha fatto ragionare"
            elif ((box.get(o) or {}).get("clearances") or 0) >= 30:
                cause = f": {art(nm(o))} ha difeso basso e compatto ({int(box[o]['clearances'])} respinte)"
            why.append((8, f"{cap(art(nm(s)))} ha creato molto meno del previsto: {fx(xg[s])} xG contro {fx(L)} attesi{cause}."))
        elif xg[s] > 1.5 * L and xg[s] - L >= .7:
            extra = ""
            if red and red["s"] == o:
                extra = ", anche per la superiorità numerica"
            why.append((8, f"{cap(art(nm(s)))} ha creato più del previsto: {fx(xg[s])} xG contro {fx(L)} attesi{extra}."))
    # concretezza e portieri
    for s in ("home", "away"):
        o = other(s)
        if gl[s] - xg[s] >= 1.0:
            why.append((6, f"{cap(art(nm(s)))} ha segnato più di quanto valessero le occasioni ({gl[s]} gol con {fx(xg[s])} xG)."))
        elif xg[s] - gl[s] >= (1.5 if gl[s] > gl[o] else .8):
            sv = int((box.get(o) or {}).get("saves") or 0)
            why.append((6, f"{cap(art(nm(s)))} ha sprecato: {fx(xg[s])} xG per {gl[s]} gol"
                           + (f", {plural(len(big[s]), 'occasione nitida fallita', 'occasioni nitide fallite')}" if big[s] else "")
                           + (f"; il portiere {art(nm(o), 'di')} ha fatto {sv} parate" if sv >= 4 else "") + "."))
    early = [g for g in goals if (g["t"] or 99) <= 15]
    if early:
        g = early[0]
        why.append((4, f"Il gol {mp('del', g['m'])} ({short(g['w'])}) ha messo subito la partita sui binari {art(nm(g['s']), 'di')}."))
    # titolari su cui contava il pronostico e che non sono partiti (formazione probabile o stimata, cambi all'ultimo)
    for s, ns in (not_started or {}).items():
        pg = sum(p for _, p in ns)
        if pick != out and pick != "X" and S[pick] == s and pg >= .2:
            why.append((6, f"Il pronostico contava su {', '.join(short(n) for n, _ in ns)} tra i titolari {art(nm(s), 'di')}, ma non sono partiti dall'inizio."))
    # come sono arrivati i gol inattesi
    if pick != out:
        surprise = [g for g in goals if out != "X" and g["s"] == S[out] or out == "X" and pick != "X" and g["s"] != S[pick]]
        if surprise:
            labs = {}
            for g in surprise:
                labs.setdefault(g["lab"].lower(), []).append(g["m"])
            who = S[out] if out != "X" else other(S[pick])
            why.append((5, f"I gol {art(nm(who), 'di')}: " + "; ".join(f"{k} ({', '.join(v)})" for k, v in labs.items()) + "."))
    # il pronostico: giusto ma prudente, o sicuro e sbagliato
    probs = {"1": f["p1"], "X": f["px"], "2": f["p2"]}
    if pick == out and probs[out] < .45 and xgp[{"1": 0, "X": 1, "2": 2}[out]] >= .8:
        why.append((3, f"Il pronostico era giusto ma troppo prudente: dava questo esito al {round(probs[out] * 100)}%, "
                       f"mentre con le occasioni create sarebbe uscito nel {round(xgp[{'1': 0, 'X': 1, '2': 2}[out]] * 100)}% dei casi."))
    if pick == out:
        if field == out:
            k, title = "ok", "Pronostico giusto, e il campo lo conferma"
            lead = (f"{cap(art(nm(S[out])))} ha creato più occasioni ({fx(xg[S[out]])} xG a {fx(xg[other(S[out])])}), come previsto."
                    if out != "X" else f"Partita equilibrata anche nelle occasioni ({fx(xg['home'])} a {fx(xg['away'])} xG).")
        else:
            k, title = "fortuna", "Pronostico giusto, ma con un aiuto"
            lead = (f"Per le occasioni la partita era {art(nm(S[field]), 'di')} ({fx(xg[S[field]])} xG a {fx(xg[other(S[field])])}): il risultato ha premiato chi ne ha create meno."
                    if field != "X" else f"Le occasioni dicevano pareggio ({fx(xg['home'])} a {fx(xg['away'])} xG): la vittoria è arrivata dagli episodi.")
    elif pre_field == pick and pick != "X":
        k, title = "campo", "Pronostico sbagliato: l'espulsione ha cambiato la partita"
        lead = f"Fino al rosso a {short(red.get('w'))} ({red.get('m')}) la partita andava come previsto, con {art(nm(S[pick]))} più pericolos{adj(nm(S[pick]), 'o', 'a')}."
    elif field == pick:
        k, title = "campo", "Pronostico sbagliato nel risultato, non nel gioco"
        lead = (f"{cap(art(nm(S[pick])))} ha creato di più ({fx(xg[S[pick]])} xG a {fx(xg[other(S[pick])])}), come previsto, ma non è bastato."
                if pick != "X" else f"Le occasioni sono state equilibrate ({fx(xg['home'])} a {fx(xg['away'])} xG), come previsto, ma un episodio ha deciso.")
    else:
        k, title = "letta", "Qui il pronostico ha letto male la partita"
        if field == "X":
            lead = f"Partita più equilibrata del previsto: occasioni {fx(xg['home'])} a {fx(xg['away'])} xG."
        else:
            fs = S[field]
            lead = f"Il campo ha detto {nm(fs)}: {fx(xg[fs])} xG contro {fx(xg[other(fs)])}, mentre il pronostico dava " + \
                   (f"avanti {art(nm(S[pick]))}." if pick != "X" else "il pareggio.")
    gtot, ltot = hs + as_, (f.get("lh") or 0) + (f.get("la") or 0)
    tail = f"Gol: attesi {fx(ltot, 1)}, segnati {gtot}, occasioni da {fx(xg['home'] + xg['away'], 1)} xG."
    why = [t for _, t in sorted(why, key=lambda x: -x[0])]
    return {"k": k, "title": title, "lead": lead, "why": why[:4], "goals": tail, "field": field}


# ---------- profili di stagione: come segna e come subisce ogni squadra ----------

def profiles(matches):
    """matches: [{"ids": {home, away}, "goals": goals_of(...), "us": tiri Understat, "ev": cronaca}] ->
    {id squadra: {"n": partite, "gf": {categoria: gol}, "ga": {...}, "tf": {etichetta: gol}, "ta": {...},
    "xgf": {situazione: xG}, "xga": {...}, "late": [fatti, subiti dall'80'], "early": [fatti, subiti entro il 15'],
    "err": {rigori causati, autogol, palle perse}, "fb": [tiri in contropiede fatti, subiti], "nus": partite con Understat}}."""
    P = {}
    for mm in matches:
        ids = mm.get("ids") or {}
        for s in ("home", "away"):
            p = P.setdefault(str(ids.get(s)), {"n": 0, "nus": 0, "gf": {}, "ga": {}, "tf": {}, "ta": {}, "xgf": {}, "xga": {},
                                               "late": [0, 0], "early": [0, 0], "err": {}, "fb": [0, 0], "zf": {}, "za": {}, "nz": 0})
            p["n"] += 1
        for g in mm.get("goals") or []:
            f, a = P[str(ids.get(g["s"]))], P[str(ids.get(other(g["s"])))]
            f["gf"][g["cat"]] = f["gf"].get(g["cat"], 0) + 1
            a["ga"][g["cat"]] = a["ga"].get(g["cat"], 0) + 1
            for t in g["tags"]:
                f["tf"][t] = f["tf"].get(t, 0) + 1
                a["ta"][t] = a["ta"].get(t, 0) + 1
            if (g.get("t") or 0) >= 80:
                f["late"][0] += 1
                a["late"][1] += 1
            if (g.get("t") or 99) <= 15:
                f["early"][0] += 1
                a["early"][1] += 1
            if g.get("lab") == "Errore":
                key = {"rigore": "rigori causati", "autogol": "autogol"}.get(g["cat"], "palle perse")
                a["err"][key] = a["err"].get(key, 0) + 1
        us = mm.get("us") or {}
        if us.get("home") or us.get("away"):
            for s in ("home", "away"):
                P[str(ids.get(s))]["nus"] += 1
            if any(len(x) > 9 for s in ("home", "away") for x in us.get(s) or []):
                for s in ("home", "away"):
                    f, a = P[str(ids.get(s))], P[str(ids.get(other(s)))]
                    f["nz"] += 1
                    for x in us.get(s) or []:
                        z = zone(x[8], x[9]) if len(x) > 9 and x[3] != "OwnGoal" and x[4] != "Penalty" else None
                        if not z:
                            continue
                        for side in (f["zf"], a["za"]):
                            c = side.setdefault(z, [0, 0.0, 0])
                            c[0] += 1
                            c[1] = round(c[1] + x[2], 3)
                            c[2] += x[3] == "Goal"
        for s in ("home", "away"):
            f, a = P[str(ids.get(s))], P[str(ids.get(other(s)))]
            for x in us.get(s) or []:
                if x[3] == "OwnGoal":
                    continue
                sit = {"FromCorner": "piazzati", "SetPiece": "piazzati", "DirectFreekick": "piazzati", "Penalty": "rigori"}.get(x[4], "azione")
                f["xgf"][sit] = round(f["xgf"].get(sit, 0) + x[2], 3)
                a["xga"][sit] = round(a["xga"].get(sit, 0) + x[2], 3)
        for e in (mm.get("ev") or {}).get("ev") or []:
            if e["k"] in ("shot", "goal", "wood") and e.get("sit") == "contropiede" and e.get("s"):
                P[str(ids.get(e["s"]))]["fb"][0] += 1
                P[str(ids.get(other(e["s"])))]["fb"][1] += 1
    return P


def _cats_line(d, verb):
    tot = sum(d.values())
    if not tot:
        return f"Nessun gol {verb}."
    parts = [(d.get("azione", 0), "su azione"), (d.get("corner", 0) + d.get("punizione", 0), "da palla inattiva"),
             (d.get("contropiede", 0), "in contropiede"), (d.get("rigore", 0), "su rigore"), (d.get("autogol", 0), "su autogol")]
    return f"{tot} gol {verb}: " + ", ".join(f"{n} {t}" for n, t in sorted(parts, key=lambda x: -x[0]) if n) + "."


def err_txt(err):
    one = {"rigori causati": "rigore causato", "autogol": "autogol", "palle perse": "palla persa"}
    return ", ".join(f"{v} {one.get(k, k) if v == 1 else k}" for k, v in err.items())


def profile_text(p, zr=None, n_t=20):
    """Frasi brevi per la scheda della squadra: come segna, come subisce, difetti e armi ricorrenti, zone di tiro.
    zr: posizioni in lega per zona (zone_ranks)."""
    out = {"segna": _cats_line(p.get("gf") or {}, "fatti"), "subisce": _cats_line(p.get("ga") or {}, "subiti"), "note": []}
    if zr and zr.get("za"):
        ra, rf, va, vf = zr["za"].get("mezzo"), zr["zf"].get("mezzo"), zr["va"].get("mezzo"), zr["vf"].get("mezzo")
        if ra and ra <= 3:
            out["note"].append(f"Concede troppo in mezzo all'area: {fx(va)} xG a partita da area piccola e centro dell'area, rigori esclusi ({ra}ª più esposta).")
        elif ra and ra >= n_t - 2:
            out["note"].append(f"Protegge bene il centro dell'area: {fx(va)} xG a partita concessi lì ({n_t - ra + 1}ª meno esposta).")
        if rf and rf <= 3:
            out["note"].append(f"Arriva spesso a tirare in mezzo all'area: {fx(vf)} xG a partita da lì ({rf}ª in lega).")
        zf = p.get("zf") or {}
        tot = sum(c[0] for c in zf.values())
        if tot >= 30 and (zf.get("fuori") or [0])[0] / tot >= .5:
            out["note"].append(f"Tira molto da fuori: {round((zf['fuori'][0]) / tot * 100)}% dei tiri, spesso segno che fatica a entrare in area.")
    ta, tf = p.get("ta") or {}, p.get("tf") or {}
    err = p.get("err") or {}
    if sum(err.values()) >= 2:
        out["note"].append(f"Errori individuali costati gol: {err_txt(err)}.")
    if ta.get("testa", 0) >= 3:
        out["note"].append(f"Soffre i colpi di testa: {ta['testa']} gol subiti così.")
    if tf.get("testa", 0) >= 3:
        out["note"].append(f"Pericolosa di testa: {tf['testa']} gol segnati così.")
    if ta.get("ribattuta", 0) >= 2:
        out["note"].append(f"Lenta sulle seconde palle: {ta['ribattuta']} gol subiti su ribattuta.")
    if (p.get("late") or [0, 0])[1] >= 3:
        out["note"].append(f"Cala nel finale: {p['late'][1]} gol subiti dall'80' in poi.")
    if (p.get("late") or [0, 0])[0] >= 3:
        out["note"].append(f"Non molla mai: {p['late'][0]} gol segnati dall'80' in poi.")
    if (p.get("early") or [0, 0])[1] >= 3:
        out["note"].append(f"Parte piano: {p['early'][1]} gol subiti nel primo quarto d'ora.")
    return out


def zone_ranks(P):
    """Per ogni squadra la posizione in lega per xG a partita creati (zf) e concessi (za) in ogni zona, dal più alto,
    più «in mezzo all'area» (area piccola + centro). -> {id: {"zf": {zona: pos}, "za": {...}}}, valori a partita."""
    out = {t: {"zf": {}, "za": {}, "vf": {}, "va": {}} for t in P}
    for key, rk, vk in (("zf", "zf", "vf"), ("za", "za", "va")):
        for z in [z for z, _ in ZONES] + ["mezzo"]:
            vals = {}
            for t, p in P.items():
                if not p.get("nz"):
                    continue
                d = p.get(key) or {}
                v = (d.get("piccola", [0, 0])[1] + d.get("centro", [0, 0])[1]) if z == "mezzo" else (d.get(z) or [0, 0])[1]
                vals[t] = v / p["nz"]
            for i, t in enumerate(sorted(vals, key=lambda t: -vals[t])):
                out[t][rk][z] = i + 1
                out[t][vk][z] = round(vals[t], 3)
    return out


def league_ranks(P, key, sub):
    """Posizione di ogni squadra per un valore a partita del profilo (es. xG da calci piazzati), dal più alto."""
    vals = {t: (p.get(key) or {}).get(sub, 0) / max(1, p.get("nus") or p["n"]) for t, p in P.items()}
    order = sorted(vals, key=lambda t: -vals[t])
    return {t: i + 1 for i, t in enumerate(order)}, vals


def keys_for(P, hid, aid, names):
    """Chiavi della prossima partita dalle partite giocate: dove l'arma di una incontra un difetto dell'altra.
    names: {id: nome}. -> [{"t": titolo, "x": testo}] (al massimo 3)."""
    hid, aid = str(hid), str(aid)
    if hid not in P or aid not in P or min(P[hid]["n"], P[aid]["n"]) < 3:
        return []
    n_t = len(P)
    rf, vf = league_ranks(P, "xgf", "piazzati")
    ra, va = league_ranks(P, "xga", "piazzati")
    out = []
    for att, dfn in ((hid, aid), (aid, hid)):
        A, D = P[att], P[dfn]
        an, dn = names.get(att, "?"), names.get(dfn, "?")
        spf = A["gf"].get("corner", 0) + A["gf"].get("punizione", 0)
        spa = D["ga"].get("corner", 0) + D["ga"].get("punizione", 0)
        if (rf[att] <= 4 or spf >= 3) and (ra[dfn] <= 4 or spa >= 3):
            a_txt = (f"{cap(art(an))} crea molto da calci piazzati ({fx(vf[att])} xG a partita, {rf[att]}ª su {n_t}"
                     + (f", {spf} gol" if spf else "") + ")") if rf[att] <= 4 else f"{cap(art(an))} ha già segnato {spf} gol da calci piazzati"
            d_txt = (f"{art(dn)} li soffre ({fx(va[dfn])} xG concessi a partita, tra i {ra[dfn] if ra[dfn] > 3 else 3} peggiori"
                     + (f"; {plural(spa, 'gol subito', 'gol subiti')} così" if spa else "") + ")") if ra[dfn] <= 4 else f"{art(dn)} ne ha già subiti {spa} così"
            out.append((3 + spf + spa, {"t": "Palle inattive", "x": f"{a_txt} e {d_txt}."}))
        cf, ca = A["gf"].get("contropiede", 0), D["ga"].get("contropiede", 0)
        if cf + A["fb"][0] / 4 >= 2.5 and ca + D["fb"][1] / 4 >= 2:
            out.append((2 + cf + ca, {"t": "Ripartenze", "x": f"{cap(art(an))} colpisce in contropiede ({cf} gol, {A['fb'][0]} tiri) "
                                                            f"e {art(dn)} si fa trovare {adj(dn, 'scoperto', 'scoperta')} ({plural(ca, 'gol subito', 'gol subiti')}, {D['fb'][1]} tiri concessi così)."}))
        err = sum(D["err"].values())
        if err >= 3:
            out.append((err, {"t": "Errori", "x": f"{cap(art(dn))} ha già regalato {err} gol con errori individuali ({err_txt(D['err'])})."}))
        if A["tf"].get("testa", 0) >= 3 and D["ta"].get("testa", 0) >= 2:
            out.append((A["tf"]["testa"] + D["ta"]["testa"], {"t": "Gioco aereo", "x": f"{cap(art(an))} segna spesso di testa ({A['tf']['testa']} gol) e {art(dn)} ne ha già subiti {D['ta']['testa']} così."}))
        if A["late"][0] >= 3 and D["late"][1] >= 2:
            out.append((A["late"][0] + D["late"][1], {"t": "Finale", "x": f"{cap(art(an))} segna spesso negli ultimi minuti ({A['late'][0]} gol dall'80') e {art(dn)} cala ({D['late'][1]} subiti)."}))
    out.sort(key=lambda x: -x[0])
    seen, res = set(), []
    for _, k in out:
        if k["t"] not in seen:
            seen.add(k["t"])
            res.append(k)
    return res[:3]


def round_summary(reads, rnd=None):
    """Com'è andata una giornata: gol per tipo, perché sono nati, pronostici e perché. reads: [lettura]."""
    if not reads:
        return None
    goals = [g for r in reads for g in r.get("goals") or []]
    cats, labs = {}, {}
    for g in goals:
        k = "palla inattiva" if g["cat"] in ("corner", "punizione") else g["cat"]
        cats[k] = cats.get(k, 0) + 1
        labs[g["lab"]] = labs.get(g["lab"], 0) + 1
    vs = [r["verdict"] for r in reads if r.get("verdict")]
    word = {"azione": "su azione", "palla inattiva": "da palla inattiva", "contropiede": "in contropiede", "rigore": "su rigore", "autogol": "autogol"}
    out = {"round": rnd, "n": len(reads), "goals": len(goals), "cats": sorted(cats.items(), key=lambda x: -x[1]),
           "labs": sorted(labs.items(), key=lambda x: -x[1]),
           "verdicts": {k: sum(1 for v in vs if v["k"] == k) for k in ("ok", "fortuna", "campo", "letta")}}
    txt = [f"{plural(len(goals), 'gol', 'gol')} in {plural(len(reads), 'partita', 'partite')}: "
           + ", ".join(f"{n} {word[k]}" for k, n in out["cats"]) + "."]
    why = {"Errore": "errori individuali (rigori causati, autogol, palle perse)", "Palla inattiva": "palle inattive",
           "Seconda palla": "seconde palle non allontanate", "Difesa superata": "difese superate da cross, filtranti o inserimenti",
           "Transizione": "contropiedi", "Prodezza": "prodezze (tiri difficili)", "Giocata individuale": "giocate individuali",
           "Azione manovrata": "azioni manovrate"}
    top = [f"{n} da {why.get(k, k.lower())}" for k, n in out["labs"] if n >= 2][:5] or [f"{n} da {why.get(k, k.lower())}" for k, n in out["labs"][:3]]
    txt.append("Perché sono nati: " + ", ".join(top) + ".")
    if vs:
        v = out["verdicts"]
        right = v["ok"] + v["fortuna"]
        wrong = v["campo"] + v["letta"]
        txt.append(f"Pronostici: {right} esiti giusti su {len(vs)}" + (f" ({v['fortuna']} con l'aiuto degli episodi)" if v["fortuna"] else "") + "."
                   + (f" Dei {wrong} sbagliati, {v['campo']} avevano letto bene il campo (episodi, espulsioni o occasioni sprecate) e {v['letta']} no."
                      if wrong else ""))
    out["text"] = txt
    return out
