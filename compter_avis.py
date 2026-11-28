"""Compte les avis « J'ai aimé / Pas aimé » des utilisateurs d'Écran Libre.

Les avis sont dans Firebase (Firestore, collection « avis ») : un document par
téléphone et par film, avec les champs film (identifiant YouTube) et avis
(« oui » ou « non »). Ce script les lit avec la clé du robot (secret GitHub
FIREBASE_CLE) et écrit les totaux par film dans avis.json :

    {"mis_a_jour": "2026-11-29T08:40:00Z", "votes": 37, "films": {"abc123": [34, 3], ...}}

robot.py ajoute ensuite ces totaux au catalogue (avis_oui, avis_non).

Ne bloque jamais le robot : sans clé, sans réseau ou en cas d'erreur, l'ancien
avis.json est gardé tel quel. La clé n'est jamais affichée.
Lancé une fois par jour (grand passage du matin) et lors des lancements à la main.
Coût Firebase : 1 lecture par avis (gratuit jusqu'à 50 000 lectures par jour).
"""

import base64
import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone

DOSSIER = os.path.dirname(os.path.abspath(__file__))
FICHIER_AVIS = os.path.join(DOSSIER, "avis.json")
MAX_AVIS = 45000          # on reste sous la limite gratuite de 50 000 lectures par jour
PAR_PAGE = 300


def _b64(donnees):
    return base64.urlsafe_b64encode(donnees).rstrip(b"=").decode()


def jeton_d_acces(cle):
    """Échange la clé du compte de service contre un jeton d'accès Google (1 heure)."""
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import padding

    maintenant = int(time.time())
    entete = _b64(json.dumps({"alg": "RS256", "typ": "JWT"}).encode())
    contenu = _b64(json.dumps({
        "iss": cle["client_email"],
        "scope": "https://www.googleapis.com/auth/datastore",
        "aud": cle.get("token_uri", "https://oauth2.googleapis.com/token"),
        "iat": maintenant,
        "exp": maintenant + 3600,
    }).encode())
    a_signer = f"{entete}.{contenu}".encode()
    prive = serialization.load_pem_private_key(cle["private_key"].encode(), password=None)
    signature = _b64(prive.sign(a_signer, padding.PKCS1v15(), hashes.SHA256()))
    corps = urllib.parse.urlencode({
        "grant_type": "urn:ietf:params:oauth:grant-type:jwt-bearer",
        "assertion": f"{entete}.{contenu}.{signature}",
    }).encode()
    requete = urllib.request.Request(cle.get("token_uri", "https://oauth2.googleapis.com/token"), data=corps)
    with urllib.request.urlopen(requete, timeout=30) as reponse:
        return json.load(reponse)["access_token"]


def lire_les_avis(projet, jeton):
    """Renvoie la liste des (film, avis) de la collection « avis »."""
    base = (f"https://firestore.googleapis.com/v1/projects/{projet}"
            f"/databases/(default)/documents/avis")
    avis, page = [], None
    while True:
        parametres = [("pageSize", PAR_PAGE), ("mask.fieldPaths", "film"), ("mask.fieldPaths", "avis")]
        if page:
            parametres.append(("pageToken", page))
        requete = urllib.request.Request(base + "?" + urllib.parse.urlencode(parametres),
                                         headers={"Authorization": f"Bearer {jeton}"})
        with urllib.request.urlopen(requete, timeout=60) as reponse:
            donnees = json.load(reponse)
        for doc in donnees.get("documents", []):
            champs = doc.get("fields", {})
            avis.append((champs.get("film", {}).get("stringValue"), champs.get("avis", {}).get("stringValue")))
        page = donnees.get("nextPageToken")
        if not page:
            return avis
        if len(avis) >= MAX_AVIS:
            print(f"Plus de {MAX_AVIS} avis : lecture arrêtée pour rester gratuit (à optimiser).")
            return avis


def totaux(avis):
    """{film: [oui, non]} à partir des (film, avis). Les avis mal formés sont ignorés."""
    resultat = {}
    for film, valeur in avis:
        if not isinstance(film, str) or not (5 <= len(film) <= 20) or valeur not in ("oui", "non"):
            continue
        compte = resultat.setdefault(film, [0, 0])
        compte[0 if valeur == "oui" else 1] += 1
    return resultat


def ecrire(films, votes):
    with open(FICHIER_AVIS, "w", encoding="utf-8") as f:
        json.dump({"mis_a_jour": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                   "votes": votes, "films": dict(sorted(films.items()))},
                  f, ensure_ascii=False, separators=(",", ":"))


def main():
    brut = os.environ.get("FIREBASE_CLE", "").strip()
    if not brut:
        print("Avis Écran Libre : pas de clé FIREBASE_CLE, on garde les derniers chiffres.")
        if not os.path.exists(FICHIER_AVIS):
            ecrire({}, 0)
        return
    try:
        cle = json.loads(brut)
        jeton = jeton_d_acces(cle)
        avis = lire_les_avis(cle["project_id"], jeton)
    except Exception as erreur:   # jamais bloquant ; le message ne contient pas la clé
        nom = type(erreur).__name__
        detail = f" (code {erreur.code})" if isinstance(erreur, urllib.error.HTTPError) else ""
        print(f"Avis Écran Libre : lecture impossible ({nom}{detail}), on garde les derniers chiffres.")
        if not os.path.exists(FICHIER_AVIS):
            ecrire({}, 0)
        return
    films = totaux(avis)
    valides = sum(o + n for o, n in films.values())
    ecrire(films, valides)
    print(f"Avis Écran Libre : {valides} avis lus, {len(films)} films notés "
          f"({sum(1 for o, n in films.values() if o + n >= 5)} avec au moins 5 avis).")


if __name__ == "__main__":
    main()
    sys.exit(0)
