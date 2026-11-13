"""MyCombo: tre combinazioni di giocate sulla stessa partita (Serie A e Premier).
Pezzo di model.py (diviso il 13/11/2026): si usa come model.mycombo, importare sempre model."""
import itertools
import math

import model
from model import NB_R, TOT_CAL, VALUE_W, clamp, fmt, nb_over, score_matrix


# ---------- MyCombo: tre combinazioni di giocate sulla stessa partita (Serie A e Premier) ----------

# Chieste dall'utente il 27/10/2026: per ogni partita di Serie A e Premier tre MyCombo di Sisal (più giocate della
# stessa partita, una quota sola) vicine a quota 10, 15 e 20, fatte solo di giocate che il modello dà come probabili,
# con i mercati che Sisal offre nelle MyCombo: esito, gol, gol di squadra, multigol, giocatori «o chi entra al suo
# posto» (segna, segna o fa assist, tiri, tiri in porta), tiri e tiri in porta, angoli (anche «in entrambi i tempi»),
# punti cartellini di squadra e della partita. Mai statistiche dei giocatori senza il sostituto né cartellini dei
# singoli (richiesta dell'utente). Le quote di Sisal non si leggono in automatico (la loro API risponde 403 ai
# programmi): la quota della combo si stima con COMBO_Q e COMBO_K, misurati componendo combo vere su Sisal.
COMBO_LEAGUES = ("Serie A", "Premier League")
COMBO_TARGETS = (10, 15, 20)
COMBO_TOL = .10                      # quota stimata entro il 10% dall'obiettivo
# giocate probabili, ma non quasi certe (sotto 1,10 alzano poco la quota). Dal 27/10 sera niente giocate sotto il 65%
# per arrivare alla quota (richiesta dell'utente: «leva giocate più difficili e poco probabili»; al 70% non si arriva
# a 15 e 20 in quasi nessuna partita)
COMBO_PMIN, COMBO_PMAX = .65, .92
# (probabilità minima, giocate sui giocatori solo se alzano la quota di COMBO_BOOST): se a una quota non si arriva, si
# accettano prima i tiri che la alzano poco, poi giocate fino al 62%, mai sotto
COMBO_PSTEPS = ((.65, True), (.65, False), (.62, False))
# Quanto Sisal fa pagare ogni tipo di giocata rispetto al modello: (1 / quota Sisal) / probabilità del modello, mediana
# sulle giocate tra 50% e 95% di 5 partite di Serie A lette il 27/10/2026 (n tra 4 e 61 per tipo). I tiri dei
# giocatori sono i più cari (1,20: Sisal li paga come se uscissero il 20% più spesso di quanto dice il modello, che
# su questi è tarato entro 2-4 punti), i punti cartellini i più giusti (1,01).
COMBO_Q = {"esito": 1.04, "gol": 1.06, "gg": 1.10, "golsq": 1.08, "angoli": 1.07, "angoliET": 1.03, "angoli2": 1.10,
           "porta": 1.07, "portaET": 1.09, "porta2": 1.05, "tiri": 1.07, "cart": 1.01, "cart2": 1.14,
           "gioc_gol": 1.03, "gioc_tiri": 1.20, "gioc_tiri2": 1.20 ** 2}
# Quota MyCombo di Sisal = prodotto delle quote stimate delle giocate (1 / (p × COMBO_Q), mai sotto 1,02), diviso per
# il legame tra le giocate sui gol (probabilità insieme dalla matrice / prodotto delle singole: Sisal le valuta
# insieme), × COMBO_K. Sui tiri dei giocatori Sisal non sconta il legame (Venezia-Inter con 15 giocate, quasi tutte
# tiri dell'Inter: 19,16 contro 15,54 del prodotto delle quote singole). Nelle 8 combo composte il 27/10/2026 la
# MyCombo vale da 0,89 a 1,51 volte il prodotto delle quote vere; con le quote stimate K va da 0,67 a 1,16 per le combo
# di giocate probabili (Milan-Bologna, Frosinone-Lecce, Genoa-Juventus, Monza-Napoli, Venezia-Inter con 8 e 15
# giocate) e arriva a 1,8-2,2 dove il modello vede le giocate molto più probabili di Sisal (Parma-Udinese,
# Fiorentina-Atalanta). La stima sbaglia quindi di ±30%: la quota vera si vede componendo la combo.
COMBO_K = .9
# Tiri dei giocatori per alzare la quota, soprattutto della squadra favorita (richiesta dell'utente del 27/10 sera,
# come nelle sue schedine): fino a COMBO_PLAYERS giocatori, per ognuno «almeno n tiri», «almeno n tiri in porta» o le
# due insieme (probabilità calcolata insieme: i tiri in porta sono una parte dei tiri). Nella scelta ogni loro giocata vale
# COMBO_FAV in più se il giocatore è della favorita (COMBO_BOTH se non c'è una favorita netta, COMBO_OTHER se è
# dell'altra squadra). Favorita: probabilità di vittoria del pronostico più 0,03 per ogni chiave tattica («forze contro
# debolezze») che vince, con almeno COMBO_FAV_GAP di distacco.
COMBO_PLAYERS = 10
COMBO_FAV, COMBO_BOTH, COMBO_OTHER, COMBO_FAV_GAP = .3, .2, .05, .05
COMBO_BOOST = 1.05                   # quota stimata minima di una giocata su un giocatore (1,10 per tiri + tiri in porta)
COMBO_GOALS = 3                      # giocate sui gol (esito, gol, gol di squadra) in una combo, al massimo
# tiri del giocatore «o chi entra al suo posto»: chi entra tira come lui, dispersione 5. Prova del 27/10/2026 sulle 61
# partite con formazione ufficiale dello storico di Serie A e Premier (1.120 titolari, 422 sostituiti, ritrovati 500
# cambi su 513): tra previsto e vero 2-4 punti di scarto medio per «almeno 1, 2, 3 tiri», 4 per i tiri in porta
COMBO_SUB, COMBO_R_PLAYER = 1.0, 5
COMBO_H1 = .45                       # quota del primo tempo di tiri in porta e angoli
# tiri e tiri in porta di una squadra secondo i gol che segna, rispetto alla sua media (1.136 partite-squadra di 7
# campionati, 2026/27, misurate il 27/10/2026): 0 gol × 0,92 e × 0,72, 1 gol 0,97 e 0,93, 2 gol 1,02 e 1,10, 3 gol
# 1,06 e 1,20, 4 o più 1,17 e 1,39. Nelle combo legano i tiri (soprattutto in porta) all'esito e ai gol.
COMBO_GOAL_SHOTS = (.92, .97, 1.02, 1.06, 1.17)
COMBO_GOAL_SOT = (.72, .93, 1.10, 1.20, 1.39)


def pois_ge(mu, k):
    """P(conteggio di Poisson con media mu almeno k)."""
    return 1 - sum(math.exp(-mu) * mu ** i / math.factorial(i) for i in range(k)) if mu > 0 else 0.0


def combo_inputs(lh, la, vol, cards, rho):
    """Quello che serve alle giocate di una partita: matrice dei risultati, tiri, tiri in porta, angoli e gialli attesi."""
    mat = score_matrix(lh, la, rho)
    return {"cells": [(i, j, v) for i, row in enumerate(mat) for j, v in enumerate(row) if v > 1e-9], "lh": lh, "la": la,
            "vol": vol, "cards": cards}


def combo_prob(spec, X):
    """Probabilità di una giocata (spec) con gli ingressi X di combo_inputs."""
    kind = spec[0]
    if kind == "goal":
        return sum(v for i, j, v in X["cells"] if spec[1](i, j))
    if kind == "nb":     # tiri, tiri in porta, angoli: della partita (t) o di una squadra, sopra o sotto la linea
        _, k, who, line, over = spec
        mh, ma = X["vol"][k]
        mu, r = ((mh + ma) * TOT_CAL, NB_R[(k, 2)]) if who == "t" else (mh if who == "h" else ma, NB_R[(k, 1)])
        po = nb_over(mu, line, r)
        return po if over else 1 - po
    if kind == "et":     # almeno n in entrambi i tempi
        _, k, who, n = spec
        mh, ma = X["vol"][k]
        mu, r = ((mh + ma) * TOT_CAL, NB_R[(k, 2)]) if who == "t" else (mh if who == "h" else ma, NB_R[(k, 1)])
        return nb_over(mu * COMBO_H1, n - .5, r) * nb_over(mu * (1 - COMBO_H1), n - .5, r)
    if kind == "both":   # entrambe le squadre almeno n
        _, k, n = spec
        mh, ma = X["vol"][k]
        return nb_over(mh, n - .5, NB_R[(k, 1)]) * nb_over(ma, n - .5, NB_R[(k, 1)])
    ch, ca = X["cards"][0] + .07, X["cards"][1] + .07   # punti cartellini: gialli più un po' di rossi (valgono 2)
    if kind == "cards":
        _, who, line, over = spec
        po = nb_over(ch + ca, line, NB_R[("cards", 2)]) if who == "t" else nb_over(ch if who == "h" else ca, line, NB_R[("cards", 1)])
        return po if over else 1 - po
    if kind == "bothcards":
        return pois_ge(ch, spec[1]) * pois_ge(ca, spec[1])
    raise ValueError(kind)


def nb_pmf(mu, n, r):
    """P(conteggio = n) per una binomiale negativa con media mu e dispersione r."""
    return math.exp(math.lgamma(n + r) - math.lgamma(r) - math.lgamma(n + 1) + r * math.log(r / (r + mu)) + n * math.log(mu / (r + mu)))


def binom_ge(n, p, k):
    """P(binomiale(n, p) almeno k)."""
    if k <= 0:
        return 1.0
    if n < k:
        return 0.0
    return 1 - sum(math.comb(n, i) * p ** i * (1 - p) ** (n - i) for i in range(k))


def combo_goals(P):
    """Gol attesi per le combo: quelli del pronostico avvicinati alle quote del mercato come per le giocate singole
    (VALUE_W al modello, il resto al mercato) quando ci sono: 1X2 e la linea di over/under dei bookmaker. Il pronostico
    resta quello del solo modello. -> (gol attesi casa, ospite, True se c'era il mercato)"""
    M = P.get("market") or {}
    if None in (M.get("p1"), M.get("px"), M.get("p2")):
        return P["lh"], P["la"], False
    rho = model.RHO_CUP if P.get("cup") else model.RHO

    def probs(lh, la):
        mat = score_matrix(lh, la, rho)
        cells = [(i, j, v) for i, row in enumerate(mat) for j, v in enumerate(row)]
        return cells, sum(v for i, j, v in cells if i > j), sum(v for i, j, v in cells if i < j)
    t1 = VALUE_W * P["p1"] + (1 - VALUE_W) * M["p1"]
    t2 = VALUE_W * P["p2"] + (1 - VALUE_W) * M["p2"]
    ou = M.get("ou") or {}
    tov = line = None
    if ou.get("over") and ou.get("under") and ou.get("line"):
        line = ou["line"]
        pmk = (1 / ou["over"]) / (1 / ou["over"] + 1 / ou["under"])
        cells, _, _ = probs(P["lh"], P["la"])
        tov = VALUE_W * sum(v for i, j, v in cells if i + j > line) + (1 - VALUE_W) * pmk

    def err(lh, la):
        cells, p1, p2 = probs(lh, la)
        e = (p1 - t1) ** 2 + (p2 - t2) ** 2
        if tov is not None:
            e += (sum(v for i, j, v in cells if i + j > line) - tov) ** 2
        return e
    best = (err(P["lh"], P["la"]), P["lh"], P["la"])
    for span in (.5, .12, .03):   # griglia sempre più fine attorno al migliore
        _, h0, a0 = best
        for dh in range(-5, 6):
            for da in range(-5, 6):
                lh, la = h0 * (1 + span * dh / 5), a0 * (1 + span * da / 5)
                if lh > .05 and la > .05:
                    e = err(lh, la)
                    if e < best[0]:
                        best = (e, lh, la)
    return best[1], best[2], True


def combo_full(X, legs, NMAX=45):
    """Probabilità che escano tutte le giocate di una combo. Gol, esito e marcatori dalla matrice dei risultati (i gol
    della squadra divisi tra i giocatori). Per ogni squadra, i tiri dei suoi giocatori e i suoi tiri e tiri in porta
    sono parti dei tiri della squadra (binomiale negativa, NB_R), che a loro volta crescono con i gol che segna
    (COMBO_GOAL_SHOTS, COMBO_GOAL_SOT): così escono più spesso insieme tra loro e con i gol. Ogni giocata resta con la
    sua probabilità tarata; il resto è indipendente."""
    gl = [l["spec"][1] for l in legs if l["spec"][0] == "goal"]
    pl = [l["ply"] for l in legs if l.get("ply")]
    cells = X["cells"]
    T = {}
    for si, side in ((0, "home"), (1, "away")):
        mu = X["vol"]["shots"][si]
        th_t = min(X["vol"]["shotsOnTarget"][si] / mu, 1.0) if mu else 0
        fns = []
        for l in legs:
            s = l["spec"]
            if s[0] in ("pnb", "pair") and l.get("side") == side and mu:
                if s[0] == "pnb":
                    sh, n_, sot = min(s[1] / mu, 1.0), s[2], s[3] == "sot"
                    fns.append(lambda N, rk, sh=sh, n_=n_, sot=sot: binom_ge(N, min(sh * (rk if sot else 1), 1.0), n_))
                else:
                    _, ls, th, a, b = s
                    sh = min(ls / mu, 1.0)
                    fns.append(lambda N, rk, sh=sh, th=th, a=a, b=b: sum(
                        math.comb(N, m) * sh ** m * (1 - sh) ** (N - m) * binom_ge(m, min(th * rk, 1.0), b) for m in range(a, N + 1)))
            elif s[0] == "nb" and s[2] == ("h" if si == 0 else "a") and s[4] and s[1] in ("shots", "shotsOnTarget"):
                if s[1] == "shots":
                    fns.append(lambda N, rk, L=s[3]: 1.0 if N > L else 0.0)
                else:
                    fns.append(lambda N, rk, L=s[3]: binom_ge(N, min(th_t * rk, 1.0), int(L) + 1))
        if not fns:
            continue
        pk = [0.0] * 5
        for i, j, v in cells:
            pk[min(i if si == 0 else j, 4)] += v
        ns = sum(p * f for p, f in zip(pk, COMBO_GOAL_SHOTS)) or 1
        no = sum(p * f for p, f in zip(pk, COMBO_GOAL_SOT)) or 1
        cond, marg = [], [0.0] * len(fns)
        for k in range(5):
            fs, fo = COMBO_GOAL_SHOTS[k] / ns, COMBO_GOAL_SOT[k] / no
            pm = [nb_pmf(mu * fs, N, NB_R[("shots", 1)]) for N in range(NMAX + 1)]
            vals = [[fn(N, fo / fs) for N in range(NMAX + 1)] for fn in fns]
            cond.append(sum(pm[N] * math.prod(v[N] for v in vals) for N in range(NMAX + 1)))
            for t, v in enumerate(vals):
                marg[t] += pk[k] * sum(pm[N] * v[N] for N in range(NMAX + 1))
        mm = math.prod(marg)
        T[si] = [c / mm if mm > 0 else 1.0 for c in cond]
    tot = 0.0
    for i, j, v in cells:
        if not all(f(i, j) for f in gl):
            continue
        for side, k in (("home", i), ("away", j)):
            ss = [s for sd, s in pl if sd == side]
            if len(ss) == 1:
                v *= 1 - (1 - ss[0]) ** k
            elif len(ss) == 2:
                v *= 1 - (1 - ss[0]) ** k - (1 - ss[1]) ** k + max(0.0, 1 - ss[0] - ss[1]) ** k
        for si, k in ((0, i), (1, j)):
            if si in T:
                v *= T[si][min(k, 4)]
        tot += v
    for l in legs:
        if l["spec"][0] not in ("goal", "ply"):
            tot *= l["p"]
    return min(tot, 1.0)


def pair_prob(ls, th, a, b):
    """P(il giocatore fa almeno a tiri e almeno b tiri in porta): tiri binomiale negativa (media ls, COMBO_R_PLAYER),
    ognuno in porta con probabilità th."""
    tot = 0.0
    for n in range(a, 41):
        pin = 1 - (1 - th) ** n if b == 1 else 1 - (1 - th) ** n - n * th * (1 - th) ** (n - 1)
        tot += nb_pmf(ls, n, COMBO_R_PLAYER) * pin
    return tot


def combo_legs(P, names, X):
    """Tutte le giocate possibili della partita: {g: gruppo (una per gruppo in una combo), k: testo, spec, ply,
    q: quanto Sisal la fa pagare rispetto al modello (COMBO_Q), c: come si controlla sul risultato (combo_check; una
    coppia tiri + tiri in porta ne ha due)}."""
    hn, an = names["home"], names["away"]
    L = []

    def add(g, k, spec, c, ply=None, q=None, side=None):
        L.append({"g": g, "k": k, "spec": spec, "c": c, "ply": ply, "q": COMBO_Q[q or g], "side": side})
    for k, key, f in ((f"1 · vince {hn}", "1", lambda i, j: i > j), ("X · pareggio", "X", lambda i, j: i == j),
                      (f"2 · vince {an}", "2", lambda i, j: i < j), (f"1X · {hn} o pareggio", "1X", lambda i, j: i >= j),
                      (f"X2 · {an} o pareggio", "X2", lambda i, j: i <= j), ("12 · non finisce pari", "12", lambda i, j: i != j)):
        add("esito", k, ("goal", f), ["esito", key])
    for line in (1.5, 2.5, 3.5, 4.5):
        add("gol", f"Over {fmt(line, 1)}", ("goal", lambda i, j, l=line: i + j > l), ["tot", line, "o"])
        add("gol", f"Under {fmt(line, 1)}", ("goal", lambda i, j, l=line: i + j < l), ["tot", line, "u"])
    for lo, hi in ((1, 3), (1, 4), (2, 4), (2, 5), (3, 5)):
        add("gol", f"Multigol {lo}-{hi}", ("goal", lambda i, j, lo=lo, hi=hi: lo <= i + j <= hi), ["mg", "t", lo, hi])
    add("gg", "Goal · segnano entrambe", ("goal", lambda i, j: i > 0 and j > 0), ["gg", 1])
    add("gg", "NoGoal · almeno una non segna", ("goal", lambda i, j: i == 0 or j == 0), ["gg", 0])
    for side, nm in (("h", hn), ("a", an)):
        sg = (lambda i, j: i) if side == "h" else (lambda i, j: j)
        for line in (.5, 1.5, 2.5):
            add("gol" + side, f"{nm} over {fmt(line, 1)} gol", ("goal", lambda i, j, l=line, sg=sg: sg(i, j) > l),
                ["sq", side, line, "o"], q="golsq")
            add("gol" + side, f"{nm} under {fmt(line, 1)} gol", ("goal", lambda i, j, l=line, sg=sg: sg(i, j) < l),
                ["sq", side, line, "u"], q="golsq")
        for lo, hi in ((1, 2), (1, 3), (2, 4)):
            add("gol" + side, f"Multigol {nm} {lo}-{hi}", ("goal", lambda i, j, lo=lo, hi=hi, sg=sg: lo <= sg(i, j) <= hi),
                ["mg", side, lo, hi], q="golsq")
    # tiri e tiri in porta (Sisal nelle MyCombo ha solo gli over), angoli: linee x,5 attorno alla media
    title = {"shots": ("tiri", "tiri"), "shotsOnTarget": ("porta", "tiri in porta"), "corners": ("angoli", "angoli")}
    for k, (g, t) in title.items():
        mh, ma = X["vol"][k]
        for who, mu, nm in (("t", (mh + ma) * TOT_CAL, ""), ("h", mh, " " + hn), ("a", ma, " " + an)):
            base = math.floor(mu) + .5
            for line in (base - 2, base - 1, base, base + 1, base + 2):
                if line < .5:
                    continue
                add(g, f"Over {fmt(line, 1)} {t}{nm}", ("nb", k, who, line, True), ["nb", k, who, line, 1])
                if k == "corners":
                    add(g, f"Under {fmt(line, 1)} {t}{nm}", ("nb", k, who, line, False), ["nb", k, who, line, 0])
    # niente angoli «in entrambi i tempi»: ESPN non dà gli angoli per tempo, e una combo che non si può controllare sul
    # risultato non serve a verificare il modello (i tiri in porta per tempo invece vengono dalla cronaca)
    for who, nm in (("h", hn), ("a", an)):
        for n in (1, 2):
            add("porta", f"{nm} almeno {n} tir{'o' if n == 1 else 'i'} in porta in entrambi i tempi", ("et", "shotsOnTarget", who, n),
                ["et", "shotsOnTarget", who, n], q="portaET")
    for n in (2, 3, 4):
        add("angoli", f"Entrambe almeno {n} angoli", ("both", "corners", n), ["both", "corners", n], q="angoli2")
        add("porta", f"Entrambe almeno {n} tiri in porta", ("both", "shotsOnTarget", n), ["both", "shotsOnTarget", n], q="porta2")
    ch, ca = X["cards"]
    for who, mu, nm in (("t", ch + ca + .14, ""), ("h", ch + .07, " " + hn), ("a", ca + .07, " " + an)):
        for line in (math.floor(mu) - .5, math.floor(mu) + .5, math.floor(mu) + 1.5):
            if line < .5:
                continue
            add("cart", f"Over {fmt(line, 1)} punti cartellini{nm}", ("cards", who, line, True), ["cards", who, line, 1])
            add("cart", f"Under {fmt(line, 1)} punti cartellini{nm}", ("cards", who, line, False), ["cards", who, line, 0])
    for n in (1, 2):
        add("cart", f"Entrambe almeno {n} punt{'o' if n == 1 else 'i'} cartellini", ("bothcards", n), ["bothcards", n], q="cart2")
    # giocatori titolari previsti, «o chi entra al suo posto»: per i minuti che restano tira e segna come lui. La loro
    # quota dei gol è rispetto ai gol attesi del pronostico (le combo possono spostare quelli della squadra)
    for side, lam_t in (("home", P["lh"]), ("away", P["la"])):
        for q in (P.get("players") or {}).get(side) or []:
            if q.get("pos") == "G" or not q.get("min"):
                continue
            f90 = 1 + (90 / q["min"] - 1) * COMBO_SUB
            nm, g, pid = q["name"], f"pl{q['id']}", q["id"]
            lg, la_ = (q.get("lamG") or 0) * f90, (q.get("lamA") or 0) * f90
            if lg:
                add(g, f"{nm} (o chi entra al suo posto) segna", ("ply",), ["ply", pid, "g"], ply=(side, min(lg / lam_t, .95)),
                    q="gioc_gol", side=side)
            if lg + la_:
                add(g, f"{nm} (o chi entra al suo posto) segna o fa assist", ("ply",), ["ply", pid, "ga"],
                    ply=(side, min((lg + la_) / lam_t, .95)), q="gioc_gol", side=side)
            for n in (1, 2, 3, 4):
                if q.get("shots"):
                    add(g, f"{nm} (o chi entra al suo posto) almeno {n} tir{'o' if n == 1 else 'i'}", ("pnb", q["shots"] * f90, n, "shots"),
                        ["pl", pid, "shots", n], q="gioc_tiri", side=side)
            for n in (1, 2):
                if q.get("sot"):
                    add(g, f"{nm} (o chi entra al suo posto) almeno {n} tir{'o' if n == 1 else 'i'} in porta",
                        ("pnb", q["sot"] * f90, n, "sot"), ["pl", pid, "sot", n], q="gioc_tiri", side=side)
            if q.get("shots") and q.get("sot"):
                ls, th = q["shots"] * f90, min(q["sot"] / q["shots"], 1.0)
                for a in (2, 3, 4):
                    for b in (1, 2):
                        if b < a:
                            add(g, [f"{nm} (o chi entra al suo posto) almeno {a} tiri",
                                    f"{nm} (o chi entra al suo posto) almeno {b} tir{'o' if b == 1 else 'i'} in porta"],
                                ("pair", ls, th, a, b), [["pl", pid, "shots", a], ["pl", pid, "sot", b]], q="gioc_tiri2", side=side)
    return L


def combo_joint(X, legs):
    """Probabilità che escano tutte: gol, esito e giocatori che segnano dalla matrice dei risultati (i gol della squadra
    divisi tra i giocatori secondo la loro quota); tiri, angoli e cartellini indipendenti tra loro e dai gol (per
    combinazioni di soli over la probabilità vera è un po' più alta: stima prudente)."""
    gl = [l["spec"][1] for l in legs if l["spec"][0] == "goal"]
    pl = [l["ply"] for l in legs if l.get("ply")]
    tot = 0.0
    for i, j, v in X["cells"]:
        if not all(f(i, j) for f in gl):
            continue
        for side, k in (("home", i), ("away", j)):
            ss = [s for sd, s in pl if sd == side]
            if len(ss) == 1:
                v *= 1 - (1 - ss[0]) ** k
            elif len(ss) == 2:
                v *= 1 - (1 - ss[0]) ** k - (1 - ss[1]) ** k + max(0.0, 1 - ss[0] - ss[1]) ** k
        tot += v
    for l in legs:
        if l["spec"][0] not in ("goal", "ply"):
            tot *= l["p"]
    return tot


def mycombo(A, P, names):
    """Tre combo per la partita, vicine alle quote COMBO_TARGETS su Sisal. Quota stimata di una combo = prodotto delle
    quote stimate delle sue giocate (1 / (probabilità del modello × COMBO_Q), mai sotto 1,02) × COMBO_K: Sisal non
    sconta le giocate legate tra loro. Probabilità della combo (combo_full): gol, esito e marcatori dalla matrice dei
    risultati con i gol avvicinati al mercato (combo_goals), i tiri della stessa squadra legati tra loro e ai suoi gol,
    il resto indipendente. Ogni giocata tra
    COMBO_PMIN e COMBO_PMAX; c'è sempre almeno una giocata sui gol o sull'esito e almeno un giocatore. Tra le combo
    vicine alla quota si sceglie quella con le giocate più probabili, usando i tiri dei giocatori (soprattutto della
    squadra favorita) per alzare la quota, e a parità quella con le giocate più legate a questa partita (probabilità
    contro quella di una partita qualunque della lega); la seconda e la terza riusano il meno possibile le giocate
    delle precedenti."""
    rho = model.RHO_CUP if P.get("cup") else model.RHO
    vol = {k: [P["vol"][k][0], P["vol"][k][1]] for k in ("shots", "shotsOnTarget", "corners")}
    lh_c, la_c, with_mk = combo_goals(P)
    X = combo_inputs(lh_c, la_c, vol, [P["cards"]["home"], P["cards"]["away"]], rho)
    Lg = A["L"]
    V0 = (Lg.get("shares") or {}).get("vol") or {}
    vol0 = {k: [(V0.get(k) or {}).get("home") or vol[k][0], (V0.get(k) or {}).get("away") or vol[k][1]] for k in vol}
    X0 = combo_inputs(Lg.get("HA") or P["lh"], Lg.get("AA") or P["la"], vol0, [Lg.get("yellow") or X["cards"][0]] * 2, rho)
    # squadra favorita: probabilità di vittoria del pronostico e chiavi tattiche vinte («forze contro debolezze»)
    ins = P.get("ins") or []
    sc = {s: P[pk] + .03 * sum(1 for i in ins if str(i.get("winner")) == str(P[s])) for s, pk in (("home", "p1"), ("away", "p2"))}
    fav = ("home" if sc["home"] - sc["away"] >= COMBO_FAV_GAP else "away" if sc["away"] - sc["home"] >= COMBO_FAV_GAP
           else None)
    odds1 = lambda p, q: max(1.02, 1 / (p * q))   # quota stimata su Sisal di una giocata
    legs = []
    for l in combo_legs(P, names, X):
        s = l["spec"]
        if s[0] == "ply":
            l["p"] = combo_joint(X, [l])
            p0 = l["p"]
        elif s[0] == "pnb":
            l["p"] = nb_over(s[1], s[2] - .5, COMBO_R_PLAYER)
            p0 = l["p"]
        elif s[0] == "pair":
            _, ls, th, a, b = s
            l["p"] = pair_prob(ls, th, a, b)
            l["parts"] = [nb_over(ls, a - .5, COMBO_R_PLAYER), nb_over(ls * th, b - .5, COMBO_R_PLAYER)]
            p0 = l["p"]
        else:
            l["p"], p0 = combo_prob(s, X), combo_prob(s, X0)
        pmin_all = min(p for p, _ in COMBO_PSTEPS)
        if not (pmin_all <= l["p"] <= COMBO_PMAX) or (s[0] == "pair" and min(l["parts"]) < pmin_all):
            continue
        # peso nella quota: log della quota stimata (le due giocate di una coppia ognuna con la sua)
        l["w"] = (sum(math.log(odds1(p, COMBO_Q["gioc_tiri"])) for p in l["parts"]) if s[0] == "pair"
                  else math.log(odds1(l["p"], l["q"])))
        # i tiri dei giocatori servono ad alzare la quota: quelli che la alzano meno di COMBO_BOOST (quasi certi, su Sisal
        # a 1,02-1,04) tolgono probabilità senza dare niente, e si usano solo se non c'è altro modo
        l["weak"] = bool(l.get("side")) and l["w"] < math.log(COMBO_BOOST) * (2 if s[0] == "pair" else 1)
        # valore nella combo: la probabilità (per intero), più un premio ai tiri dei giocatori della favorita, che
        # così sono il primo modo per arrivare alla quota; un poco quanto la giocata è legata a questa partita
        bonus = (COMBO_BOTH if fav is None else COMBO_FAV if l["side"] == fav else COMBO_OTHER) if l.get("side") else 0.0
        bonus *= 2 if s[0] == "pair" else 1   # due giocate su Sisal
        l["v"] = math.log(l["p"]) + bonus + .1 * math.log(l["p"] / clamp(p0, .01, .99))
        legs.append(l)
    GOAL = ("esito", "gol", "gg", "golh", "gola")
    STEP = .02
    NB_ = int(math.log(max(COMBO_TARGETS) * 1.3) / STEP) + 2
    REUSE = .05    # giocata già in una combo precedente della stessa partita

    def goal_sets(goal):
        """Gruppi di giocate sui gol: da 1 a COMBO_GOALS gruppi diversi, al massimo un giocatore (segna o fa assist)."""
        out_, byg = [], {}
        for l in goal:
            byg.setdefault(l["g"], []).append(l)
        for n in range(1, COMBO_GOALS + 1):
            for groups in itertools.combinations(list(byg), n):
                if sum(1 for g in groups if g.startswith("pl")) > 1:
                    continue
                for c in itertools.product(*(byg[g] for g in groups)):
                    pj = combo_joint(X, list(c))
                    if pj > 0:
                        out_.append((c, pj))
        return out_

    def dp(stat, exclude, used):
        """Zaino a gruppi sulle statistiche: per ogni somma dei pesi nella quota (passi di STEP) e numero di
        giocatori, la scelta con il valore più alto."""
        groups = {}
        for l in stat:
            if l["g"] not in exclude:
                groups.setdefault(l["g"], []).append(l)
        best = {(0, 0): (0.0, ())}
        for g, items in groups.items():
            isp = g.startswith("pl")
            new = dict(best)
            for (b, k), (v, ch) in best.items():
                for l in items:
                    nb = b + int(round(l["w"] / STEP))
                    nk = k + isp
                    if nb >= NB_ or nk > COMBO_PLAYERS:
                        continue
                    nv = v + l["v"] - (REUSE if id(l) in used else 0)
                    if (nb, nk) not in new or nv > new[(nb, nk)][0]:
                        new[(nb, nk)] = (nv, ch + (l,))
            best = new
        return best

    def search(target, gsets, stat, used):
        """La combo con il valore più alto tra quelle con quota stimata entro COMBO_TOL da exp(target)."""
        cache, cand = {}, None
        for need_player in (True, False):
            for c, pj in gsets:
                pls = frozenset(l["g"] for l in c if l["g"].startswith("pl"))
                if pls not in cache:
                    cache[pls] = dp(stat, pls, used)
                best = cache[pls]
                vg = sum(l["v"] - (REUSE if id(l) in used else 0) for l in c)
                # Sisal conta il legame tra le giocate sui gol (più probabili insieme, quota più bassa): lo stesso con
                # la matrice dei risultati
                wg = sum(l["w"] for l in c) - math.log(pj / math.prod(l["p"] for l in c))
                # solo i passi dello zaino vicini alla quota cercata (la somma arrotondata sbaglia di qualche passo)
                lo, hi = int((target - wg - tol) / STEP) - 3, int((target - wg + tol) / STEP) + 3
                for b in range(max(lo, 0), min(hi, NB_ - 1) + 1):
                    for k in range(COMBO_PLAYERS + 1):
                        e = best.get((b, k))
                        if not e or (need_player and not (k or pls)):
                            continue
                        v, ch = e
                        if cand is not None and vg + v <= cand[0]:
                            continue
                        lw = wg + sum(l["w"] for l in ch)
                        if abs(lw - target) <= tol:
                            cand = (vg + v, c + ch, pj * math.prod(l["p"] for l in ch), math.exp(lw) * COMBO_K)
            if cand:
                return cand
        return None
    out, used = [], set()
    tol = math.log(1 + COMBO_TOL)
    pools = {}
    for T in COMBO_TARGETS:
        target = math.log(T / COMBO_K)
        cand = None
        for step in COMBO_PSTEPS:
            pmin, boost = step
            if step not in pools:
                ok = [l for l in legs if l["p"] >= pmin and (l["spec"][0] != "pair" or min(l["parts"]) >= pmin)
                      and not (boost and l["weak"])]
                goal = [l for l in ok if l["g"] in GOAL or l["spec"][0] == "ply"]
                pools[step] = (goal_sets(goal), [l for l in ok if l not in goal])
            gsets, stat = pools[step]
            cand = search(target, gsets, stat, used)
            if cand:
                break
        if not cand:
            continue
        _, chosen, pj, est = cand
        pj = combo_full(X, chosen)   # i tiri della stessa squadra escono più spesso insieme, e con i suoi gol
        used |= {id(l) for l in chosen}
        out.append({"t": T, "p": round(pj, 4), "fair": round(1 / pj, 2), "est": round(est, 1), "ev": round(pj * est - 1, 3),
                    "legs": [{"k": k, "p": round(p, 3), "c": c} for l in sorted(chosen, key=lambda l: -l["p"])
                             for k, p, c in (zip(l["k"], l["parts"], l["c"]) if l["spec"][0] == "pair" else [(l["k"], l["p"], l["c"])])]})
    return {"k": COMBO_K, "pmin": COMBO_PMIN, "fav": names[fav] if fav else None, "mk": with_mk, "items": out}
