#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Zeitreihen-Sammler.

Holt Listen von den konfigurierten Quellen, verdichtet sie je Schlüssel zu einer Zeile
und legt jeden neuen Stand als verschlüsselte Datei ab. Alle Adressen, Feldnamen und
Zugangsdaten kommen aus der Umgebung; in diesem Skript steht nichts davon.

Umgebung:
  FM_ID, FM_GEHEIM   Zugangsdaten für das Token
  FM_SCHLUESSEL      Datenschlüssel (32 Byte, Base64)
  FM_KONFIG          Einstellungen als JSON
  FM_ZIEL            Zielordner (Standard: d)
  FM_WARTEN          Minuten, die ein Lauf auf neue Stände wartet (Standard 65; 0 = nur ein Durchgang)
  FM_TAKT            Sekunden zwischen zwei Nachfragen während des Wartens (Standard 120)

Ein Lauf endet, sobald jede Quelle einen neuen Stand geliefert hat oder die Wartezeit vorbei ist.
"""
import base64
import datetime as dt
import gzip
import hashlib
import io
import json
import lzma
import math
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from email.utils import parsedate_to_datetime

from cryptography.hazmat.primitives.ciphers.aead import AESGCM

VERSION = "0.2.0"
KENNUNG = b"FMD1"
SPALTEN = ["item", "variante", "min", "markt", "s100", "s1000", "menge", "angebote", "neu", "neu_menge", "kurz"]


def sag(text):
    print(text, flush=True)


# ---------------------------------------------------------------- Abruf
class Antwort:
    def __init__(self, status, kopf, roh, fehler=""):
        self.status, self.kopf, self.roh, self.fehler = status, kopf, roh, fehler

    def json(self):
        try:
            return json.loads(self.roh.decode("utf-8"))
        except Exception:
            return None


def hole(url, params=None, kopf=None, methode="GET", daten=None, versuche=3):
    if params:
        url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    h = {"Accept-Encoding": "gzip", "User-Agent": "sammler/" + VERSION}
    h.update(kopf or {})
    letzter = ""
    for v in range(versuche):
        req = urllib.request.Request(url, data=daten, method=methode, headers=h)
        try:
            with urllib.request.urlopen(req, timeout=180) as r:
                status, hk, roh = r.status, r.headers, r.read()
        except urllib.error.HTTPError as e:
            status, hk, roh = e.code, e.headers, e.read()
        except Exception as e:
            letzter = type(e).__name__
            time.sleep(3 * (v + 1))
            continue
        if status in (429, 500, 502, 503, 504) and v < versuche - 1:
            time.sleep(5 * (v + 1))
            continue
        k = {a.lower(): b for a, b in hk.items()}
        if k.get("content-encoding", "").lower() == "gzip" and roh:
            try:
                roh = gzip.decompress(roh)
            except Exception:
                return Antwort(0, k, b"", "Antwort nicht lesbar")
        return Antwort(status, k, roh)
    return Antwort(0, {}, b"", letzter or "keine Antwort")


def hole_token(konfig, kennung, geheim):
    auth = base64.b64encode(f"{kennung}:{geheim}".encode()).decode()
    r = hole(konfig["token_url"], None, {"Authorization": "Basic " + auth, "Content-Type": "application/x-www-form-urlencoded"}, "POST", b"grant_type=client_credentials")
    tok = (r.json() or {}).get("access_token") if r.status == 200 else None
    if not tok:
        raise SystemExit(f"Kein Token erhalten (Status {r.status}).")
    return tok


# ---------------------------------------------------------------- Verdichten
class FormFehler(Exception):
    pass


def liste_aus(doc, felder):
    """Liste der Einträge eines Dokuments; ein Dokument ohne Liste gilt als leer."""
    if not isinstance(doc, dict):
        raise FormFehler("Antwort ist kein Objekt")
    eintraege = doc.get(felder["liste"])
    if eintraege is None:
        return []
    if not isinstance(eintraege, list):
        raise FormFehler("Liste hat eine unerwartete Form")
    return eintraege


def verdichte(listen, felder, max_nr_alt=None, varianten="falten"):
    """Fasst Einträge je (item, variante) zusammen.

    varianten: "falten" = alle Einträge mit Variantenliste eines Items bilden eine Zeile (variante -1),
               "einzeln" = je Variante eine Zeile, "ohne" = solche Einträge weglassen.
               Einträge ohne Variantenliste haben immer variante 0.

    Rückgabe: (zeilen, statistik). Jede Zeile hat die Spalten aus SPALTEN:
      min        günstigster Stückpreis
      markt      mengengewichteter Schnitt der günstigsten 15 % aller Stücke
      s100/s1000 Schnitt der ersten 100 / 1.000 Stücke, ohne Angebote über dem 3-fachen Mindestpreis
      menge      Stücke gesamt, angebote = Zahl der Einträge
      neu        Einträge mit höherer Nummer als beim vorigen Stand (-1 beim ersten Stand), neu_menge deren Stücke
      kurz       Einträge mit der kürzesten Restlaufzeit
    """
    f_item, f_id, f_var = felder["item"], felder["item_id"], felder["variante"]
    f_menge, f_stk, f_ges, f_lz, f_nr = felder["menge"], felder["stueckpreis"], felder["gesamtpreis"], felder["laufzeit"], felder["nr"]
    kurz_wert = felder.get("kurz_wert", "SHORT")
    gruppen = {}
    stat = {"eintraege": 0, "ohne_preis": 0, "fehlerhaft": 0, "ausgelassen": 0, "max_nr": max_nr_alt or 0}
    for eintraege in listen:
        for e in eintraege:
            stat["eintraege"] += 1
            if not isinstance(e, dict):
                stat["fehlerhaft"] += 1
                continue
            it = e.get(f_item)
            iid = it.get(f_id) if isinstance(it, dict) else it
            menge = e.get(f_menge)
            if not isinstance(iid, int) or isinstance(iid, bool) or not isinstance(menge, int) or menge < 1:
                stat["fehlerhaft"] += 1
                continue
            if e.get(f_stk):
                preis = e[f_stk]
            elif e.get(f_ges):
                preis = e[f_ges] / menge
            else:
                stat["ohne_preis"] += 1
                continue
            if not isinstance(preis, (int, float)) or preis <= 0:
                stat["fehlerhaft"] += 1
                continue
            var = it.get(f_var) if isinstance(it, dict) else None
            if isinstance(var, list) and var:
                if varianten == "ohne":
                    stat["ausgelassen"] += 1
                    continue
                variante = int(var[0]) if varianten == "einzeln" and len(var) == 1 and isinstance(var[0], int) and var[0] > 0 else -1
            else:
                variante = 0
            nr = e.get(f_nr)
            nr = nr if isinstance(nr, int) else 0
            if nr > stat["max_nr"]:
                stat["max_nr"] = nr
            g = gruppen.get((iid, variante))
            if g is None:
                g = gruppen[(iid, variante)] = [[], 0, 0, 0]          # Angebote, neu, neu_menge, kurz
            g[0].append((preis, menge))
            if max_nr_alt is not None and nr > max_nr_alt:
                g[1] += 1
                g[2] += menge
            if e.get(f_lz) == kurz_wert:
                g[3] += 1
    zeilen = []
    for (iid, variante), (angebote, neu, neu_menge, kurz) in sorted(gruppen.items()):
        angebote.sort()
        gesamt = sum(m for _, m in angebote)
        mini = angebote[0][0]
        zeilen.append((iid, variante, int(round(mini)), int(round(schnitt(angebote, max(1, math.ceil(0.15 * gesamt))))),
                       int(round(schnitt(angebote, 100, 3 * mini))), int(round(schnitt(angebote, 1000, 3 * mini))),
                       gesamt, len(angebote), neu if max_nr_alt is not None else -1, neu_menge if max_nr_alt is not None else -1, kurz))
    return zeilen, stat


def schnitt(angebote, stueck, grenze=None):
    """Mittlerer Stückpreis der günstigsten 'stueck' Stücke (aufsteigend sortierte Angebote)."""
    rest, kosten, genommen = stueck, 0.0, 0
    for preis, menge in angebote:
        if grenze is not None and preis > grenze:
            break
        k = min(rest, menge)
        kosten += k * preis
        genommen += k
        rest -= k
        if rest <= 0:
            break
    return kosten / genommen


# ---------------------------------------------------------------- Ablage
# Dateiaufbau (vor dem Verschlüsseln, LZMA-gepackt):
#   4 Byte Länge des Kopfes, Kopf als JSON, danach je Spalte ein Block ganzer Zahlen (Zickzack-Varint).
#   Kopf: {"v":1, "n":Zeilen, "spalten":[[Name, Umformung, Bytes], ...], weitere Angaben zum Stand}
#   Umformung "delta": Differenz zur Vorzeile; "minus_min": Differenz zur Spalte min.
UMFORMUNG = {"item": "delta", "markt": "minus_min", "s100": "minus_min", "s1000": "minus_min"}


def varint(werte):
    aus = bytearray()
    for v in werte:
        v = (v << 1) ^ (v >> 63)
        while v > 0x7F:
            aus.append((v & 0x7F) | 0x80)
            v >>= 7
        aus.append(v)
    return bytes(aus)


def varint_lies(roh, anzahl):
    aus, v, schub = [], 0, 0
    for b in roh:
        v |= (b & 0x7F) << schub
        if b & 0x80:
            schub += 7
        else:
            aus.append((v >> 1) ^ -(v & 1))
            v, schub = 0, 0
    if len(aus) != anzahl:
        raise ValueError("Spaltenlänge passt nicht")
    return aus


def packe(zeilen, meta):
    spalten = [list(s) for s in zip(*zeilen)] if zeilen else [[] for _ in SPALTEN]
    mini = spalten[SPALTEN.index("min")]
    bloecke, kopf_spalten = [], []
    for name, werte in zip(SPALTEN, spalten):
        art = UMFORMUNG.get(name, "")
        if art == "delta":
            werte = [w - v for w, v in zip(werte, [0] + werte[:-1])]
        elif art == "minus_min":
            werte = [w - m for w, m in zip(werte, mini)]
        block = varint(werte)
        bloecke.append(block)
        kopf_spalten.append([name, art, len(block)])
    kopf = dict(meta)
    kopf.update({"v": 1, "n": len(zeilen), "spalten": kopf_spalten})
    kb = json.dumps(kopf, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return lzma.compress(len(kb).to_bytes(4, "little") + kb + b"".join(bloecke), preset=9 | lzma.PRESET_EXTREME)


def entpacke(daten):
    roh = lzma.decompress(daten)
    kl = int.from_bytes(roh[:4], "little")
    kopf = json.loads(roh[4:4 + kl].decode("utf-8"))
    pos, spalten = 4 + kl, {}
    for name, art, laenge in kopf["spalten"]:
        werte = varint_lies(roh[pos:pos + laenge], kopf["n"])
        pos += laenge
        if art == "delta":
            summe = 0
            for i, w in enumerate(werte):
                summe += w
                werte[i] = summe
        elif art == "minus_min":
            werte = [w + m for w, m in zip(werte, spalten["min"])]
        spalten[name] = werte
    return kopf, spalten


def verschluessele(daten, schluessel):
    nonce = os.urandom(12)
    return KENNUNG + nonce + AESGCM(schluessel).encrypt(nonce, daten, KENNUNG)


def entschluessele(roh, schluessel):
    if roh[:4] != KENNUNG:
        raise ValueError("Unbekanntes Dateiformat")
    return AESGCM(schluessel).decrypt(roh[4:16], roh[16:], KENNUNG)


def lies_schluessel(text):
    try:
        s = base64.urlsafe_b64decode(text.strip() + "=" * (-len(text.strip()) % 4))
    except Exception:
        s = b""
    if len(s) != 32:
        raise SystemExit("FM_SCHLUESSEL fehlt oder hat nicht die erwartete Länge.")
    return s


def stand_zeit(kopf):
    lm = kopf.get("last-modified")
    if not lm:
        return None, None
    try:
        return lm, parsedate_to_datetime(lm).astimezone(dt.timezone.utc)
    except Exception:
        return lm, None


# ---------------------------------------------------------------- Ablauf
MAX_FEHLVERSUCHE = 3


def zahl_aus(name, standard, konfig):
    roh = os.environ.get(name)
    if roh is None or roh.strip() == "":
        roh = konfig.get(name[3:].lower(), standard)
    try:
        return max(0.0, float(roh))
    except (TypeError, ValueError):
        return float(standard)


def hole_quelle(q, alt, konfig, kopf, felder):
    """Ein Abruf einer Quelle. Rückgabe: None (unverändert) oder (lm, zeit, zeilen, stat)."""
    bedingt = dict(kopf)
    if alt.get("lm"):
        bedingt["If-Modified-Since"] = alt["lm"]
    r = hole(konfig["basis"] + q["pfade"][0], konfig.get("parameter"), bedingt)
    if r.status == 304:
        return None
    if r.status != 200:
        raise FormFehler(f"Status {r.status} {r.fehler}".strip())
    lm, zeit = stand_zeit(r.kopf)
    if lm and lm == alt.get("lm"):
        return None
    listen = [liste_aus(r.json(), felder)]
    for pfad in q["pfade"][1:]:
        x = hole(konfig["basis"] + pfad, konfig.get("parameter"), kopf)
        if x.status != 200:
            raise FormFehler(f"Status {x.status} {x.fehler} beim Zusatzabruf".strip())
        listen.append(liste_aus(x.json(), felder))
    zeilen, stat = verdichte(listen, felder, alt.get("max_nr"), konfig.get("varianten", "falten"))
    if stat["eintraege"] and stat["fehlerhaft"] > 0.02 * stat["eintraege"]:
        raise FormFehler(f"{stat['fehlerhaft']} von {stat['eintraege']} Einträgen haben eine unerwartete Form")
    if not zeilen and (alt.get("zeilen") or 0) > 0:
        raise FormFehler("leere Antwort, obwohl der vorige Stand Daten hatte")
    pruef = hashlib.sha256(repr(zeilen).encode()).hexdigest()[:16]
    if lm is None and pruef == alt.get("pruef"):
        return None
    return lm, zeit, zeilen, stat, pruef


def lauf():
    kennung, geheim = os.environ.get("FM_ID", "").strip(), os.environ.get("FM_GEHEIM", "").strip()
    if not kennung or not geheim:
        raise SystemExit("FM_ID oder FM_GEHEIM fehlt.")
    schluessel = lies_schluessel(os.environ.get("FM_SCHLUESSEL", ""))
    try:
        konfig = json.loads(os.environ.get("FM_KONFIG", ""))
        felder, quellen = konfig["felder"], konfig["quellen"]
    except Exception:
        raise SystemExit("FM_KONFIG fehlt oder ist kein gültiges JSON.")
    warten = zahl_aus("FM_WARTEN", 65, konfig) * 60
    takt = max(1.0, zahl_aus("FM_TAKT", 120, konfig))
    ziel = os.environ.get("FM_ZIEL", "d")
    os.makedirs(ziel, exist_ok=True)
    standdatei = os.path.join(ziel, "stand.json")
    try:
        with open(standdatei, encoding="utf-8") as f:
            alt_text = f.read()
        stand = json.loads(alt_text)
    except Exception:
        alt_text, stand = "", {}

    beginn = time.monotonic()
    token = hole_token(konfig, kennung, geheim)
    kopf = {"Authorization": "Bearer " + token}
    offen = [q["k"] for q in quellen]          # Quellen, die in diesem Lauf noch keinen neuen Stand geliefert haben
    fehlversuche = {k: 0 for k in offen}
    letzter_fehler = {}
    neu, durchgang = 0, 0
    while True:
        durchgang += 1
        for q in quellen:
            k = q["k"]
            if k not in offen or fehlversuche[k] >= MAX_FEHLVERSUCHE:
                continue
            alt = stand.get(k) or {}
            jetzt = dt.datetime.now(dt.timezone.utc)
            try:
                erg = hole_quelle(q, alt, konfig, kopf, felder)
                if erg is None:
                    if durchgang == 1:
                        sag(f"Quelle {k}: unverändert")
                    letzter_fehler.pop(k, None)
                    continue
                lm, zeit, zeilen, stat, pruef = erg
                zeit = zeit or jetzt
                pfad = os.path.join(ziel, zeit.strftime("%Y-%m"), zeit.strftime("%d"), f"{zeit.strftime('%H%M')}-{k}.bin")
                meta = {"q": k, "stand": zeit.strftime("%Y-%m-%dT%H:%M:%SZ"), "abruf": jetzt.strftime("%Y-%m-%dT%H:%M:%SZ"),
                        "eintraege": stat["eintraege"], "ohne_preis": stat["ohne_preis"], "erster": int(alt.get("max_nr") is None)}
                if os.path.exists(pfad):
                    sag(f"Quelle {k}: Stand {zeit.strftime('%d.%m. %H:%M')} liegt schon vor")
                else:
                    roh = verschluessele(packe(zeilen, meta), schluessel)
                    os.makedirs(os.path.dirname(pfad), exist_ok=True)
                    with open(pfad, "wb") as f:
                        f.write(roh)
                    neu += 1
                    sag(f"Quelle {k}: neuer Stand {zeit.strftime('%d.%m. %H:%M')} UTC, {stat['eintraege']} Einträge, {len(zeilen)} Zeilen, {len(roh) / 1024:.0f} KB")
                stand[k] = {"lm": lm, "max_nr": stat["max_nr"], "zeilen": len(zeilen), "pruef": pruef, "stand": meta["stand"]}
                offen.remove(k)
                letzter_fehler.pop(k, None)
            except FormFehler as e:
                fehlversuche[k] += 1
                letzter_fehler[k] = str(e)
                sag(f"Quelle {k}: FEHLER - {e}")
            except Exception as e:                               # nichts Unerwartetes darf Zugangsdaten ins Protokoll bringen
                fehlversuche[k] += 1
                letzter_fehler[k] = type(e).__name__
                sag(f"Quelle {k}: FEHLER - {type(e).__name__}")
        neu_text = json.dumps(stand, indent=1, sort_keys=True)
        if neu_text != alt_text:
            with open(standdatei, "w", encoding="utf-8") as f:
                f.write(neu_text)
            alt_text = neu_text
        aktiv = [k for k in offen if fehlversuche[k] < MAX_FEHLVERSUCHE]
        vergangen = time.monotonic() - beginn
        if not aktiv or vergangen + takt > warten:
            break
        time.sleep(takt)

    for k in offen:
        if k not in letzter_fehler and warten > 0:
            sag(f"Quelle {k}: kein neuer Stand innerhalb der Wartezeit")
    fehler = len(letzter_fehler)
    sag(f"Fertig: {neu} neue Stände, {fehler} Fehler, {durchgang} {'Durchgang' if durchgang == 1 else 'Durchgänge'}, {(time.monotonic() - beginn) / 60:.1f} Min.")
    return 1 if fehler else 0


if __name__ == "__main__":
    sys.exit(lauf())
