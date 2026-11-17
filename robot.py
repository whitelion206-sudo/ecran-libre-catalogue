"""Robot du catalogue Écran Libre.

Une fois par jour, il récupère les vidéos des chaînes listées dans chaines.json,
garde seulement les films utilisables par l'appli, et écrit catalogue.json.

Un film est gardé s'il :
- dure au moins DUREE_MIN_MINUTES minutes ;
- est public et peut être intégré dans une autre appli ;
- est autorisé en France ;
- n'est pas réservé aux adultes (ces vidéos ne se lisent pas hors de YouTube) ;
- n'a pas « VOSTFR », « bande-annonce »… dans son titre (VF uniquement) ;
- n'est pas dans exclus.txt ;
- pour les chaînes marquées « vf_seulement », a un titre qui dit qu'il est en français.

Les genres viennent du titre YouTube (ce qui suit « Film Complet en Français | »),
complétés par le genre de la chaîne (sauf « Animation », voir fiche_film).

Quand une chaîne remplace le nom du film par une phrase d'accroche, le robot
retrouve le vrai titre sur Wikidata grâce au réalisateur et aux acteurs
indiqués dans la description (voir vrais_titres).

Il cherche aussi la bande-annonce de chaque film (70 films par jour au plus,
à cause du quota de l'API YouTube), puis ajoute les « classiques » du domaine public listés dans classiques.json,
hébergés sur Wikimedia Commons (réutilisation commerciale permise).

La clé API est lue dans la variable d'environnement YOUTUBE_API_KEY
(un « secret » GitHub), jamais écrite dans ce fichier.
"""

import difflib
import html
import json
import os
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from datetime import date, datetime, timezone

API = "https://www.googleapis.com/youtube/v3/"
PAYS = "FR"
DUREE_MIN_MINUTES = 60

DOSSIER = os.path.dirname(os.path.abspath(__file__))
FICHIER_CHAINES = os.path.join(DOSSIER, "chaines.json")
FICHIER_EXCLUS = os.path.join(DOSSIER, "exclus.txt")
FICHIER_CATALOGUE = os.path.join(DOSSIER, "catalogue.json")
FICHIER_CLASSIQUES = os.path.join(DOSSIER, "classiques.json")


def appel_api(methode, parametres, cle, fatal=True):
    """Appelle l'API YouTube et renvoie la réponse JSON.

    Si fatal=False, une erreur (par exemple quota du jour épuisé) ne stoppe
    pas le robot : elle lève RuntimeError, que l'appelant peut rattraper.
    """
    parametres = dict(parametres, key=cle)
    url = API + methode + "?" + urllib.parse.urlencode(parametres)
    try:
        with urllib.request.urlopen(url, timeout=30) as reponse:
            return json.load(reponse)
    except urllib.error.HTTPError as erreur:
        detail = erreur.read().decode("utf-8", "replace")
        message = f"Erreur de l'API YouTube ({erreur.code}) sur {methode} : {detail[:300]}"
        if fatal:
            sys.exit(message)
        raise RuntimeError(message)
    except (urllib.error.URLError, TimeoutError) as erreur:
        if fatal:
            sys.exit(f"Connexion impossible à l'API YouTube sur {methode} : {erreur}")
        raise RuntimeError(str(erreur))


def duree_en_minutes(iso):
    """Convertit une durée YouTube (ex. PT1H26M39S) en minutes."""
    m = re.fullmatch(r"P(?:(\d+)D)?T?(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?", iso or "")
    if not m:
        return 0
    jours, heures, minutes, secondes = (int(x) if x else 0 for x in m.groups())
    return jours * 1440 + heures * 60 + minutes + round(secondes / 60)


# « | Film Complet en Français », « - Film COMPLET en VF »,
# « 🐎| Film Western Complet en Français », « - Film Western Complet - Acteur (1973) »
FIN_DE_TITRE = re.compile(
    r"\s*[|\-–—•]\s*(?:films?|dessins?\s+anim[ée]s?)\b(?:\s+[\w'’]+){0,3}?\s+complets?\b",
    flags=re.IGNORECASE,
)


def sans_emojis(texte):
    """Enlève les emojis et pictogrammes (🐎, 🥷, 😲…) d'un titre."""
    propre = "".join(c for c in texte
                     if unicodedata.category(c) not in ("So", "Sk", "Cs", "Co")
                     and c not in "‍️")
    return re.sub(r"\s+", " ", propre).strip()


def titre_propre(titre):
    """Garde seulement le nom du film, sans « Film complet… » ni emojis."""
    morceau = FIN_DE_TITRE.split(titre)[0]
    morceau = re.split(r"\s*\|\s*", morceau)[0]
    morceau = sans_emojis(morceau).strip(" |-–—•")
    return morceau or titre.strip()


MOTS_INTERDITS = re.compile(
    r"\bvost(?:fr)?\b|\bvo\b|version originale|sous[- ]titr|bande[- ]annonce|\btrailer\b|\bteaser\b",
    flags=re.IGNORECASE,
)

# Pour les chaînes qui mélangent français et anglais (option "vf_seulement"
# dans chaines.json) : on ne garde que les vidéos dont le titre dit qu'elles
# sont en français.
SIGNES_ANGLAIS = re.compile(
    r"full[\s-]+(?:length\s+)?movie|\benglish\b|free\s+movie",
    flags=re.IGNORECASE,
)
SIGNES_FRANCAIS = re.compile(
    r"fran[cç]ais|\bVF\b|films?\s+complets?|version\s+fran[cç]aise",
    flags=re.IGNORECASE,
)


def est_en_francais(video):
    """Vrai si la vidéo est clairement en français (titre ou langue indiquée)."""
    snippet = video.get("snippet", {})
    titre = snippet.get("title", "")
    if SIGNES_ANGLAIS.search(titre):
        return False
    if SIGNES_FRANCAIS.search(titre):
        return True
    if re.search(r"\bmovie\b", titre, flags=re.IGNORECASE):
        return False
    audio = (snippet.get("defaultAudioLanguage") or "").lower()
    langue = (snippet.get("defaultLanguage") or "").lower()
    return audio.startswith("fr") and langue.startswith("fr")


# Les catégories affichées dans l'appli. Tout genre lu dans un titre est
# ramené à l'une d'elles ; un genre inconnu est ignoré (et noté dans le journal
# du robot pour qu'on puisse l'ajouter ici plus tard).
GENRES_CONNUS = [
    "Action", "Ados", "Animation", "Arts martiaux", "Aventure", "Biopic", "Catastrophe",
    "Comédie", "Comédie dramatique", "Comédie romantique", "Documentaire", "Drame", "Famille",
    "Fantastique", "Guerre", "Historique", "Horreur", "Musical", "Nanar", "Noël",
    "Policier", "Romance", "Science-fiction", "Sport", "Thriller", "Western",
]

# Variantes et sous-genres (écrits sans accents ni majuscules) -> catégorie.
GENRES_RENOMMES = {
    # Nanar (séries B volontairement kitsch)
    "nanars": "Nanar", "film nanar": "Nanar", "cinema nanar": "Nanar",
    # Ados
    "teen": "Ados", "teen movie": "Ados", "teen movies": "Ados", "ado": "Ados",
    "adolescent": "Ados", "adolescents": "Ados", "drame adolescent": "Ados",
    # Famille / enfants
    "kids": "Famille", "kid": "Famille", "enfant": "Famille", "enfants": "Famille",
    "enfance": "Famille", "jeunesse": "Famille", "familial": "Famille", "family": "Famille",
    "equitation": "Famille", "cheval": "Famille", "chevaux": "Famille",
    "animal": "Famille", "animaux": "Famille", "chien": "Famille", "chiens": "Famille",
    # Animation
    "dessin anime": "Animation", "dessins animes": "Animation", "stop motion": "Animation",
    "animated": "Animation",
    # Science-fiction
    "sf": "Science-fiction", "sci-fi": "Science-fiction", "sci fi": "Science-fiction",
    "science fiction": "Science-fiction", "anticipation": "Science-fiction",
    "extraterrestre": "Science-fiction", "extraterrestres": "Science-fiction",
    "robot": "Science-fiction", "robots": "Science-fiction",
    # Fantastique
    "fantasy": "Fantastique", "magie": "Fantastique", "dragon": "Fantastique",
    "dragons": "Fantastique", "conte": "Fantastique", "contes": "Fantastique",
    "super heros": "Fantastique", "super-heros": "Fantastique", "superheros": "Fantastique",
    # Horreur
    "horror": "Horreur", "epouvante": "Horreur", "monstre": "Horreur", "monstres": "Horreur",
    "zombie": "Horreur", "zombies": "Horreur", "vampire": "Horreur", "vampires": "Horreur",
    "slasher": "Horreur", "gore": "Horreur", "halloween": "Horreur", "requin": "Horreur",
    "requins": "Horreur", "creature": "Horreur", "creatures": "Horreur",
    # Aventure
    "aventures": "Aventure", "adventure": "Aventure", "pirate": "Aventure",
    "pirates": "Aventure", "dinosaure": "Aventure", "dinosaures": "Aventure",
    "survie": "Aventure", "jungle": "Aventure",
    # Thriller
    "suspense": "Thriller", "mystere": "Thriller", "enquete": "Thriller",
    "psychologique": "Thriller", "espionnage": "Thriller", "espion": "Thriller",
    # Policier
    "crime": "Policier", "criminel": "Policier", "gangster": "Policier",
    "gangsters": "Policier", "mafia": "Policier", "braquage": "Policier", "polar": "Policier",
    # Comédie / drame / romance
    "comedy": "Comédie", "humour": "Comédie", "parodie": "Comédie",
    "drama": "Drame", "romantique": "Romance", "amour": "Romance", "romance": "Romance",
    "comedie dramatique": "Comédie dramatique", "comedie romantique": "Comédie romantique",
    # Autres
    "noel": "Noël", "christmas": "Noël", "fetes": "Noël",
    "kung fu": "Arts martiaux", "karate": "Arts martiaux", "martial": "Arts martiaux",
    "biographie": "Biopic", "biographique": "Biopic", "histoire vraie": "Biopic",
    "histoire": "Historique", "peplum": "Historique", "medieval": "Historique",
    "militaire": "Guerre", "war": "Guerre",
    "musique": "Musical", "comedie musicale": "Musical", "opera": "Musical", "danse": "Musical",
    "football": "Sport", "boxe": "Sport", "surf": "Sport",
    "documentary": "Documentaire",
    # Vus dans le journal du robot du 16/11/2026
    "frissons": "Horreur", "frisson": "Horreur",
    "combat": "Action", "combats": "Action", "bagarre": "Action",
    "emotion": "Drame", "emotions": "Drame",
    "survival": "Aventure", "road trip": "Aventure", "road movie": "Aventure",
    "ballet": "Musical",
    "seduction": "Romance",
    "anime": "Animation", "manga": "Animation",
    "formula 1": "Sport", "formule 1": "Sport", "f1": "Sport", "skate": "Sport",
    "course": "Sport", "courses": "Sport", "voiture": "Action", "voitures": "Action",
}

GENRES_IGNORES = {}  # genre inconnu -> nombre de fois vu (affiché dans le journal)


def sans_accents(texte):
    return unicodedata.normalize("NFKD", texte).encode("ascii", "ignore").decode().lower()


def nettoie_genre(genre):
    """Enlève les emojis et symboles (💎, ⏫…) et les espaces en trop."""
    propre = "".join(c for c in genre if c.isalnum() or c in " -'’")
    return re.sub(r"\s+", " ", propre).strip(" -'’")


def genre_normalise(genre, strict=False):
    """Ramène un genre à une catégorie de GENRES_CONNUS, ou None s'il est inconnu.
    strict=True : seulement un genre exact (ou une faute de frappe), sans
    chercher un mot connu dans une expression plus longue, et sans le noter."""
    propre = nettoie_genre(genre)
    cle = sans_accents(propre)
    if not cle:
        return None
    connus = {sans_accents(g): g for g in GENRES_CONNUS}
    if cle in GENRES_RENOMMES:
        return GENRES_RENOMMES[cle]
    if cle in connus:
        return connus[cle]
    proche = difflib.get_close_matches(cle, connus, n=1, cutoff=0.9)
    if proche:  # fautes de frappe : « Thriler », « Comedie »
        return connus[proche[0]]
    if strict:
        return None
    # Un mot connu dans une expression plus longue : on garde le plus long.
    trouves = {}
    for k, nom in list(connus.items()) + list(GENRES_RENOMMES.items()):
        if re.search(r"\b" + re.escape(k) + r"\b", cle):
            trouves[k] = nom
    if trouves:
        return trouves[max(trouves, key=len)]
    GENRES_IGNORES[propre] = GENRES_IGNORES.get(propre, 0) + 1
    return None


def genres_du_titre(titre):
    """Lit les genres écrits après « Film Complet en Français | » dans le titre YouTube."""
    morceaux = [m.strip() for m in titre.split("|")]
    for i, morceau in enumerate(morceaux):
        if re.search(r"(?:films?|dessins?\s+anim[ée]s?)\s+complets?", morceau, flags=re.IGNORECASE) \
                and i + 1 < len(morceaux):
            genres = []
            for genre in re.split(r"[,/&]|\bet\b", morceaux[i + 1]):
                genre = genre_normalise(genre)
                if genre and genre not in genres:
                    genres.append(genre)
            return genres
    # Pas de « Film complet » dans le titre (« Accroche | Sci-Fi, Action ») :
    # on prend un morceau suivant s'il ne contient QUE des genres connus.
    for morceau in morceaux[1:]:
        parties = [p for p in re.split(r"[,/&]|\bet\b", morceau) if nettoie_genre(p)]
        genres = [genre_normalise(p, strict=True) for p in parties]
        if parties and all(genres):
            return list(dict.fromkeys(genres))
    return []


def autorise_en_france(details):
    restriction = details.get("contentDetails", {}).get("regionRestriction", {})
    if "allowed" in restriction and PAYS not in restriction["allowed"]:
        return False
    if PAYS in restriction.get("blocked", []):
        return False
    return True


def est_utilisable(video, exclus):
    statut = video.get("status", {})
    contenu = video.get("contentDetails", {})
    if video["id"] in exclus:
        return False
    if MOTS_INTERDITS.search(video.get("snippet", {}).get("title", "")):
        return False
    if statut.get("privacyStatus") != "public" or not statut.get("embeddable", False):
        return False
    if contenu.get("contentRating", {}).get("ytRating") == "ytAgeRestricted":
        return False
    if duree_en_minutes(contenu.get("duration")) < DUREE_MIN_MINUTES:
        return False
    return autorise_en_france(video)


def miniature(snippet):
    vignettes = snippet.get("thumbnails", {})
    for taille in ("maxres", "standard", "high", "medium", "default"):
        if taille in vignettes:
            return vignettes[taille]["url"]
    return ""


def videos_de_la_chaine(chaine, cle):
    """Renvoie les identifiants de toutes les vidéos mises en ligne par la chaîne.
    La chaîne est donnée par son identifiant (« id » : UC…) ou par son nom
    YouTube (« handle » : @…)."""
    if chaine.get("id"):
        parametres = {"part": "contentDetails", "id": chaine["id"]}
    else:
        parametres = {"part": "contentDetails", "forHandle": chaine.get("handle", "")}
    reponse = appel_api("channels", parametres, cle)
    if not reponse.get("items"):
        print(f"Chaîne introuvable : {chaine.get('id') or chaine.get('handle')}")
        return []
    if not chaine.get("id"):
        print(f"{chaine['nom']} : identifiant {reponse['items'][0].get('id')}")
    liste = reponse["items"][0]["contentDetails"]["relatedPlaylists"]["uploads"]
    ids, page = [], None
    while True:
        parametres = {"part": "contentDetails", "playlistId": liste, "maxResults": 50}
        if page:
            parametres["pageToken"] = page
        reponse = appel_api("playlistItems", parametres, cle)
        ids += [item["contentDetails"]["videoId"] for item in reponse.get("items", [])]
        page = reponse.get("nextPageToken")
        if not page:
            return ids


def details_des_videos(ids, cle):
    details = []
    for debut in range(0, len(ids), 50):
        paquet = ids[debut:debut + 50]
        reponse = appel_api(
            "videos",
            {"part": "snippet,contentDetails,status", "id": ",".join(paquet)},
            cle,
        )
        details += reponse.get("items", [])
    return details


def sans_doublons(films):
    """Un même film peut être publié par plusieurs chaînes. On garde la copie
    de la chaîne qui vient en premier dans chaines.json (ou la plus ancienne),
    et on lui ajoute les genres des autres copies. Deux films de même titre
    mais de durées très différentes (un remake…) sont gardés tous les deux."""
    gardes = {}        # titre normalisé -> fiches gardées
    resultat = {}
    retires = []
    for fid, film in films.items():           # dans l'ordre des chaînes
        cle_titre = normalise(film["titre"])
        double = None
        for autre in gardes.get(cle_titre, []):
            if abs(film["duree_minutes"] - autre["duree_minutes"]) <= 5:
                double = autre
                break
        if double is None:
            gardes.setdefault(cle_titre, []).append(film)
            resultat[fid] = film
            continue
        for genre in film["genres"]:
            if genre not in double["genres"]:
                double["genres"].append(genre)
        double["genre"] = double["genre"] or (double["genres"][0] if double["genres"] else "")
        retires.append(f"{film['titre']} ({film['chaine']})")
    if retires:
        print(f"Doublons retirés : {len(retires)} (ex. : {', '.join(retires[:5])})")
    return resultat


# « Titre : Exeter » dans la description (pas « Titre original : … »).
TITRE_DESCRIPTION = re.compile(
    r"^[^\w\n]*titre(?:\s+(?:du\s+film|fran[cç]ais|vf))?\s*:\s*(.+?)\s*$",
    flags=re.IGNORECASE | re.MULTILINE,
)


def titre_dans_description(description):
    """Vrai titre écrit par la chaîne dans sa description, ou None."""
    m = TITRE_DESCRIPTION.search(description or "")
    if not m:
        return None
    titre = sans_emojis(m.group(1)).strip(" «»\"'“”.-–—|")
    if not titre or len(titre) > 80 or len(titre.split()) > 12:
        return None
    return titre


def genres_des_hashtags(description):
    """« #Horreur #ScienceFiction » -> ["Horreur", "Science-fiction"]
    (seulement des genres connus, les autres hashtags sont ignorés)."""
    genres = []
    for tag in re.findall(r"#([^\W\d_][\w-]*)", description or ""):
        tag = re.sub(r"(?<=[a-zà-ÿ])(?=[A-Z])", " ", tag).replace("_", " ")
        genre = genre_normalise(tag, strict=True)
        if genre and genre not in genres:
            genres.append(genre)
    return genres


def fiche_film(video, chaine):
    snippet = video["snippet"]
    description = snippet.get("description", "")
    # Les genres du titre sont les plus précis. Sinon, ceux des hashtags de la
    # description (#Horreur). Le genre de la chaîne est ajouté en plus, sauf
    # « Animation » : la chaîne Animation publie aussi des films avec de vrais
    # acteurs (ex. « Le Monstre des Sables »).
    genres = genres_du_titre(snippet.get("title", "")) or genres_des_hashtags(description)
    genre_chaine = chaine.get("genre", "")
    if genre_chaine and genre_chaine not in genres:
        if not genres:
            genres.append(genre_chaine)
        elif genre_chaine != "Animation":
            genres.append(genre_chaine)
    titre = titre_propre(snippet.get("title", ""))
    fiche_titre = {}
    vrai_titre = titre_dans_description(description)
    if vrai_titre and normalise(vrai_titre) != normalise(titre):
        # La chaîne a mis une accroche dans le titre YouTube, mais le vrai nom
        # du film dans la description : « Titre : Exeter ».
        fiche_titre = {"titre_accroche": titre}
        titre = vrai_titre
    return {
        **fiche_titre,
        "id": video["id"],
        "titre": titre,
        "titre_youtube": snippet.get("title", ""),
        "description": snippet.get("description", "")[:500],
        "duree_minutes": duree_en_minutes(video["contentDetails"].get("duration")),
        "date": snippet.get("publishedAt", ""),
        "miniature": miniature(snippet),
        "genre": genres[0] if genres else "",
        "genres": genres,
        "chaine": chaine["nom"],
        # Statut « conçu pour les enfants » de YouTube : l'appli doit couper tout
        # suivi pour ces vidéos (règles des API YouTube, III.E.4.j).
        "pour_enfants": bool(video.get("status", {}).get("madeForKids", False)),
    }


# --- Vrais titres (Wikidata) -------------------------------------------------
#
# Certaines chaînes (Ciné Nanar…) remplacent le nom du film par une phrase
# d'accroche : « Pour sauver sa fille, il va devoir traverser une planète
# condamnée ». Leur description donne alors le réalisateur et les acteurs
# (« ►Réalisation », « ►ACTEURS »). Le robot demande à Wikidata (gratuit, sans
# clé, sans quota YouTube) quel film les réunit, et prend son titre français.
# Le résultat est retenu dans catalogue.json (« titres_trouves »).

WIKIDATA_SPARQL = "https://query.wikidata.org/sparql"
MAX_DEMANDES_WIKIDATA = 150   # par jour
REESSAI_TITRE_JOURS = 30      # film non trouvé : on redemande après 30 jours
REGLE_TITRES = 2              # changer ce numéro fait tout redemander à Wikidata
TOLERANCE_DUREE_MINUTES = 15  # durée Wikidata trop différente : ce n'est pas le même film
STATS_TITRES = {"trouves": [], "pas_trouves": 0, "sans_equipe": 0, "sans_reponse": 0,
                "deux_points": 0}

VERBE_ACCROCHE = re.compile(
    r"\b(?:il|elle|ils|elles|on)\s+(?:va|vont|doit|doivent|devra|devront|veut|veulent|"
    r"est|sont|a|ont|se|s'|s’|ne|n'|n’|d[ée]couvre|d[ée]couvrent|devient|deviennent|"
    r"pense|pensait|croit|croyait|tente|tentent)\b",
    flags=re.IGNORECASE,
)


def est_une_accroche(titre):
    """Vrai si le « titre » ressemble à une phrase plutôt qu'à un nom de film.
    Une virgule ne suffit pas : « Creuse ta fosse, j'aurai ta peau » est un
    vrai titre. Il faut une phrase longue, ou « il va… », « elle doit… »."""
    mots = titre.split()
    if len(mots) >= 10:
        return True
    return len(mots) >= 6 and bool(VERBE_ACCROCHE.search(titre))


def titre_avant_deux_points(titre):
    """« Ice Road Terror : la créature rôde sur la route » -> « Ice Road Terror »."""
    m = re.match(r"^(.{2,60}?)\s+:\s+(.+)$", titre)
    if m and 1 <= len(m.group(1).split()) <= 6 and len(m.group(2).split()) >= 4:
        return m.group(1).strip()
    return None


def deja_le_bon_titre(titre_youtube, titre_wikidata):
    """Vrai si Wikidata renvoie en fait le même titre (« Ciakmull, le bâtard
    de Dodge City » / « Ciak Mull ») : la chaîne avait déjà le vrai nom."""
    a = normalise(titre_youtube).replace(" ", "")
    b = normalise(titre_wikidata).replace(" ", "")
    return bool(a and b) and (a in b or b in a or difflib.SequenceMatcher(None, a, b).ratio() >= 0.6)


def noms(ligne):
    """« Kellan Lutz, Daniel MacPherson et Isabel Lucas » -> liste de noms."""
    resultat = []
    for nom in re.split(r"[,/&;]|\set\s|\sand\s", ligne):
        nom = re.sub(r"\s+", " ", nom).strip(" .-–—:")
        if 2 <= len(nom.split()) <= 5 and len(nom) <= 60 and nom not in resultat:
            resultat.append(nom)
    return resultat


def equipe_du_film(description):
    """Lit le réalisateur et les acteurs dans la description YouTube."""
    def section(motif):
        m = re.search(r"(?:^|\n)[^\w\n]*(?:" + motif + r")\s*:?[ \t]*(?:\n\s*)?([^\n]+)",
                      description, flags=re.IGNORECASE)
        return noms(m.group(1)) if m else []
    realisateurs = section(r"r[ée]alisation|r[ée]alisateurs?|r[ée]alisatrices?|r[ée]alis[ée] par")
    acteurs = section(r"acteurs?|casting|distribution")
    return realisateurs[:2], acteurs[:5]


def requete_wikidata(realisateurs, acteurs):
    def valeurs(liste):
        liste = [n.replace("\\", "").replace('"', "") for n in liste]
        return " ".join(f'"{n}"@{langue}' for n in liste for langue in ("mul", "en", "fr"))
    lien_realisateur = ""
    if realisateurs:
        lien_realisateur = (f"VALUES ?nomReal {{ {valeurs(realisateurs)} }} "
                            "?real rdfs:label ?nomReal . ?film wdt:P57 ?real .")
    return f"""SELECT ?film (SAMPLE(?fr) AS ?titreFr) (SAMPLE(?en) AS ?titreEn)
       (SAMPLE(?d) AS ?duree) (COUNT(DISTINCT ?acteur) AS ?n) WHERE {{
  {lien_realisateur}
  VALUES ?nomActeur {{ {valeurs(acteurs)} }}
  ?acteur rdfs:label ?nomActeur .
  ?film wdt:P161 ?acteur .
  OPTIONAL {{ ?film rdfs:label ?fr . FILTER(LANG(?fr) = "fr") }}
  OPTIONAL {{ ?film rdfs:label ?en . FILTER(LANG(?en) = "en") }}
  OPTIONAL {{ ?film wdt:P2047 ?d }}
}} GROUP BY ?film ORDER BY DESC(?n) LIMIT 5"""


def appel_wikidata(requete):
    requete_http = urllib.request.Request(
        WIKIDATA_SPARQL + "?" + urllib.parse.urlencode({"query": requete}),
        headers={"User-Agent": USER_AGENT, "Accept": "application/sparql-results+json"},
    )
    with urllib.request.urlopen(requete_http, timeout=60) as reponse:
        return json.load(reponse)


def chercher_vrai_titre(realisateurs, acteurs, duree_youtube=None):
    """Renvoie le titre du seul film qui réunit ce réalisateur et ces acteurs,
    ou None (rien trouvé, ou plusieurs films possibles)."""
    lignes = appel_wikidata(requete_wikidata(realisateurs, acteurs))["results"]["bindings"]
    films = []
    for ligne in lignes:
        titre = (ligne.get("titreFr") or ligne.get("titreEn") or {}).get("value", "").strip()
        n = int(ligne.get("n", {}).get("value", 0))
        try:
            duree = float(ligne.get("duree", {}).get("value", ""))
            if duree > 400:          # parfois donnée en secondes
                duree = duree / 60
        except ValueError:
            duree = None
        if titre:
            films.append((n, titre, duree))
    # Il faut deux acteurs en commun (un seul ne suffit pas : un réalisateur
    # tourne souvent plusieurs films avec le même acteur). Exception : la
    # description ne cite qu'un acteur, et le réalisateur est connu.
    minimum = 1 if (realisateurs and len(acteurs) == 1) else 2
    if not films or films[0][0] < minimum:
        return None
    if len(films) > 1 and films[1][0] == films[0][0]:
        return None  # deux films aussi probables : on ne devine pas
    n, titre, duree = films[0]
    if duree and duree_youtube and abs(duree - duree_youtube) > TOLERANCE_DUREE_MINUTES:
        return None  # pas la même durée : pas le même film
    return titre


def vrais_titres(films, textes_films, ancien_catalogue):
    """Remplace les phrases d'accroche par le vrai titre quand Wikidata le connaît.
    Renvoie la mémoire des recherches."""
    aujourd_hui = datetime.now(timezone.utc).date()
    ancienne = ancien_catalogue.get("titres_trouves", {})
    memoire = {}
    deja_demande = {}   # même équipe (film publié sur plusieurs chaînes) : une seule demande
    demandes = 0
    pannes = 0
    panne = False

    def demander(realisateurs, acteurs, duree):
        """Demande à Wikidata, avec un second essai si le serveur hoquette."""
        nonlocal demandes, pannes, panne
        cle = (tuple(realisateurs), tuple(acteurs), duree)
        if cle in deja_demande:
            return deja_demande[cle]
        for essai in (1, 2):
            try:
                demandes += 1
                titre = chercher_vrai_titre(realisateurs, acteurs, duree)
                time.sleep(1)  # Wikidata demande de ne pas aller trop vite
                deja_demande[cle] = titre
                return titre
            except Exception as erreur:
                if essai == 1:
                    time.sleep(5)
                    continue
                pannes += 1
                if pannes >= 3:  # Wikidata vraiment en panne : on réessaiera demain
                    print(f"Wikidata indisponible ({erreur}) : vrais titres remis à demain.")
                    panne = True
                raise

    for fid, film in films.items():
        if not est_une_accroche(film["titre"]):
            continue
        avant = titre_avant_deux_points(film["titre"])
        if avant:  # le vrai titre est déjà là, avant « : »
            STATS_TITRES["deux_points"] += 1
            film["titre_accroche"] = film["titre"]
            film["titre"] = avant
            continue
        r = ancienne.get(fid)
        if r is not None and r.get("regle") != REGLE_TITRES:
            r = None  # trouvé avec une ancienne règle : on redemande
        if r is not None:
            memoire[fid] = r
        a_demander = r is None
        if r and not r.get("titre"):
            try:
                a_demander = (aujourd_hui - date.fromisoformat(r.get("date", ""))).days \
                    >= REESSAI_TITRE_JOURS
            except ValueError:
                a_demander = True
        if a_demander and not panne and demandes < MAX_DEMANDES_WIKIDATA:
            realisateurs, acteurs = equipe_du_film(textes_films.get(fid, ""))
            titre = None
            if not acteurs:
                STATS_TITRES["sans_equipe"] += 1
            else:
                try:
                    titre = demander(realisateurs, acteurs, film.get("duree_minutes"))
                except Exception:
                    STATS_TITRES["sans_reponse"] += 1
                    continue  # pas de réponse : on redemandera au prochain passage
                if titre and deja_le_bon_titre(film["titre"], titre):
                    titre = None
                if titre:
                    STATS_TITRES["trouves"].append(f"{film['titre']} → {titre}")
                else:
                    STATS_TITRES["pas_trouves"] += 1
            r = memoire[fid] = {"titre": titre, "date": aujourd_hui.isoformat(),
                                "regle": REGLE_TITRES}
        if r and r.get("titre"):
            film["titre_accroche"] = film["titre"]
            film["titre"] = r["titre"]
    gardes = sum(1 for f in films.values() if f.get("titre_accroche"))
    print(f"Vrais titres : {gardes} films avec une phrase d'accroche corrigée "
          f"({STATS_TITRES['deux_points']} grâce au titre écrit avant « : », "
          f"{len(STATS_TITRES['trouves'])} trouvés aujourd'hui sur Wikidata, "
          f"{STATS_TITRES['pas_trouves']} inconnus de Wikidata, "
          f"{STATS_TITRES['sans_equipe']} sans acteurs dans la description, "
          f"{STATS_TITRES['sans_reponse']} sans réponse de Wikidata).")
    for ligne in STATS_TITRES["trouves"][:20]:
        print("  ✓ " + ligne)
    return memoire


# --- Bandes-annonces ---------------------------------------------------------
#
# Une recherche YouTube coûte 100 points de quota sur 10 000 par jour.
# Le robot en fait donc au plus MAX_RECHERCHES par jour, en commençant par les
# films les plus récents, et retient le résultat dans catalogue.json
# (« recherches_bandes_annonces ») pour ne pas chercher deux fois.
# Chaque jour, les bandes-annonces déjà trouvées sont revérifiées (1 point
# par paquet de 50) : une vidéo supprimée ou bloquée disparaît de l'appli.

MAX_RECHERCHES = 70
# Version de la règle de choix. 2 = titre exact ; 3 = + VF écrite dans le titre
# + preuve que c'est le même film (acteurs, réalisateur ou année) ;
# 4 = comme 3, mais la VOSTFR est aussi acceptée quand il n'y a pas de VF ;
# 5 = la preuve n'est plus obligatoire (les descriptions des films en ont
# rarement), mais une année différente fait refuser la vidéo, et les vidéos
# avec une preuve passent en premier ;
# 6 = dans la description du film, on ignore les années égales ou postérieures
# à sa mise en ligne sur YouTube (« © 2026 »…) : ce n'est pas l'année du film.
# Changer ce numéro efface toutes les recherches faites avec l'ancienne règle
# (trouvées ou non) : elles sont refaites avec la nouvelle.
REGLE_BA = 6
REESSAI_JOURS = 90          # film sans bande-annonce : on recherche après 90 jours
DUREE_MAX_BA_MINUTES = 6

MOTS_BA = re.compile(r"bande[- ]?annonce|\btrailer\b|\bteaser\b", flags=re.IGNORECASE)
# Les films gratuits sur YouTube ne sont pas des films Netflix, Prime Video ou
# Disney+ : une bande-annonce de ces plateformes parle d'un autre film.
MOTS_BA_REFUSES = re.compile(
    r"netflix|prime\s*video|disney\s*\+|disney\s*plus|"
    r"english|anglais|r[ée]action|critique|review|analyse|"
    r"explication|fan[- ]?made|parodie|r[ée]sum[ée]|making[- ]of|interview|extrait",
    flags=re.IGNORECASE,
)
# « Bande-annonce » seul ne dit pas la langue : le titre doit dire VF, FR,
# français… ou VOSTFR (version originale sous-titrée en français).
SIGNES_VOSTFR = re.compile(
    r"\bvost(?:fr|f)?\b|\bvo\s*st\s*fr?\b|\bvo\b.*sous[- ]?titr|sous[- ]?titr\w*\s+(?:en\s+)?fran[cç]ais",
    flags=re.IGNORECASE,
)
SIGNES_VF = re.compile(r"\bVFF?\b|\bFR\b|fran[cç]ais|version\s+fran[cç]aise", flags=re.IGNORECASE)


def langue_du_titre(titre):
    """« VF », « VOSTFR », ou None si le titre ne dit pas que c'est en français."""
    if SIGNES_VOSTFR.search(titre):
        return "VOSTFR"
    if SIGNES_VF.search(titre):
        return "VF"
    return None

# Mots qui commencent souvent par une majuscule sans être un nom de personne :
# ils ne comptent pas comme preuve que deux vidéos parlent du même film.
MOTS_PAS_DES_NOMS = set("""
a à au aux avec avant apres alors au aussi bande annonce annonces bientot blu bonus ca car ce ces
cette chaine cinema cine complet complete dans de des decouvrez disponible distribution du dvd d elle
elles en entre et exclusif exclusive facebook film films francais francaise france hd il ils instagram
je jamais la le les leur lui mais meme nous on ou official officiel officielle par pendant plus pour
quand qui que regardez retrouvez sa sans se ses si son sortie sous suivez sur synopsis teaser tiktok
toujours tous tout trailer twitter un une vf vff video videos vod vous youtube abonnez abonne
prime amazon netflix disney canal plus apple tv allocine filmsactu bande-annonce genre duree date
lundi mardi mercredi jeudi vendredi samedi dimanche janvier fevrier mars avril mai juin juillet aout
septembre octobre novembre decembre realise realisateur realisatrice casting avec acteurs actrices
nationalite americain americaine francais anglais britannique version originale long metrage
vost vostfr vostf vo st fr titre titres titree titrees
""".split())


def preuves(texte, mots_titre):
    """Années et noms propres (deux mots à majuscule qui se suivent : « Bruce
    Willis ») d'un texte. Sert à vérifier qu'une bande-annonce et un film qui
    portent le même titre sont bien le même film."""
    texte = html.unescape(texte or "")
    annees = set(re.findall(r"\b(?:19[2-9]\d|20[0-4]\d)\b", texte))
    noms = set()
    for phrase in re.split(r"[\n.,;:!?()\[\]{}|/«»\"“”•–—]+", texte):
        mots = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ-]+", phrase)
        for a, b in zip(mots, mots[1:]):
            if not (a[0].isupper() and b[0].isupper()):
                continue
            na, nb = normalise(a), normalise(b)
            if len(na) < 2 or len(nb) < 2:
                continue
            if any(m in MOTS_PAS_DES_NOMS or m in mots_titre for m in (na + " " + nb).split()):
                continue
            noms.add(f"{na} {nb}")
    return annees, noms


def meme_film(texte_film, texte_ba, titre_film, annee_mise_en_ligne=None):
    """Compare un film et une bande-annonce qui portent le même titre.
    annee_mise_en_ligne : année où le film complet a été publié sur YouTube.
    Les années égales ou postérieures dans sa description (« © 2026 »,
    « nouveauté 2026 »…) ne sont pas l'année du film : on les ignore.
    Renvoie (verdict, détail) :
      ("preuve", …)  un même nom (acteur, réalisateur…) ou la même année ;
      ("conflit", …) les deux donnent une année, et elles sont différentes ;
      ("neutre", "")  rien pour confirmer ni pour contredire."""
    mots_titre = set(normalise(titre_film).split())
    annees_f, noms_f = preuves(texte_film, mots_titre)
    annees_b, noms_b = preuves(texte_ba, mots_titre)
    if annee_mise_en_ligne:
        annees_f = {a for a in annees_f if int(a) < annee_mise_en_ligne}
    communs = sorted(noms_f & noms_b)
    if communs:
        return "preuve", ", ".join(communs[:2])
    proches = sorted(a for a in annees_f for b in annees_b if abs(int(a) - int(b)) <= 1)
    if proches:
        return "preuve", "année " + proches[0]
    if annees_f and annees_b:
        return "conflit", f"film {min(annees_f)} / vidéo {min(annees_b)}"
    return "neutre", ""


STATS_BA = {"pas_francais": 0, "autre_langue": 0, "conflit": 0, "avec_preuve": 0,
            "sans_preuve": 0}
EXEMPLES_REFUSES = []


def normalise(texte):
    return re.sub(r"[^a-z0-9]+", " ", sans_accents(html.unescape(texte or ""))).strip()


# Mots qu'on accepte autour du titre du film dans le titre d'une bande-annonce.
# Les articles (le, la, the…) et les chiffres n'en font pas partie : « The Head
# Hunter » ou « Rage 2 » ne sont pas « Head Hunter » ou « Rage ».
MOTS_AUTOUR_BA = {
    "bande", "annonce", "annonces", "bandeannonce", "trailer", "teaser", "vf", "vff",
    "officielle", "officiel", "official", "francais", "francaise", "french", "hd", "4k",
    "uhd", "nouvelle", "nouveau", "exclusive", "exclusif", "film", "en", "version",
    "de", "du", "d", "fr", "et", "vost", "vostfr", "vostf", "vo", "st", "stfr", "sous",
    "titre", "titres", "titree", "titrees",
} | {mot for g in GENRES_CONNUS for mot in normalise(g).split()}
SEPARATEURS_BA = re.compile(r"\s?\|\s?")  # « Titre | Bande-annonce VF | Chaîne »


def titre_correspond(titre_film, titre_video):
    """Vrai si la vidéo porte le titre exact du film, entouré seulement de mots
    comme « bande-annonce », « VF », l'année ou le genre."""
    cible = normalise(titre_film).split()
    if not cible:
        return False
    for morceau in [titre_video] + SEPARATEURS_BA.split(titre_video):
        mots = normalise(morceau).split()
        for debut in range(len(mots) - len(cible) + 1):
            if mots[debut:debut + len(cible)] != cible:
                continue
            autour = mots[:debut] + mots[debut + len(cible):]
            if all(m in MOTS_AUTOUR_BA or re.fullmatch(r"(19|20)\d\d", m) for m in autour):
                return True
    return False


def chercher_bande_annonce(film, cle, exclus):
    """Renvoie les vidéos candidates (id, titre, langue), les VF en premier,
    puis les VOSTFR."""
    cible = normalise(film["titre"])
    if len(cible) < 2:
        return []
    # 10 résultats coûtent autant de quota que 5 (100 points par recherche).
    reponse = appel_api("search", {
        "part": "snippet", "q": f'{film["titre"]} bande annonce', "type": "video",
        "maxResults": 10, "regionCode": PAYS, "relevanceLanguage": "fr",
        "videoEmbeddable": "true", "videoDuration": "short",
    }, cle, fatal=False)
    candidats = []
    for item in reponse.get("items", []):
        id_video = item.get("id", {}).get("videoId")
        titre = html.unescape(item.get("snippet", {}).get("title", ""))
        if not id_video or id_video in exclus or id_video == film["id"]:
            continue
        if not MOTS_BA.search(titre) or MOTS_BA_REFUSES.search(titre):
            continue
        if not titre_correspond(film["titre"], titre):
            continue  # la vidéo doit porter exactement le titre du film
        langue = langue_du_titre(titre)
        if langue is None:
            STATS_BA["pas_francais"] += 1
            continue  # « bande-annonce » seul ne veut pas dire « en français »
        candidats.append((id_video, titre, langue))
    candidats.sort(key=lambda c: 0 if c[2] == "VF" else 1)
    return candidats


def bandes_annonces_lisibles(ids, cle, exclus):
    """Parmi ces vidéos, garde celles qu'on peut lire dans l'appli en France.
    Renvoie {id: détails de la vidéo} (titre et description compris)."""
    bonnes = {}
    ids = list(dict.fromkeys(ids))
    for debut in range(0, len(ids), 50):
        reponse = appel_api("videos", {
            "part": "snippet,contentDetails,status", "id": ",".join(ids[debut:debut + 50]),
        }, cle, fatal=False)
        for video in reponse.get("items", []):
            statut = video.get("status", {})
            contenu = video.get("contentDetails", {})
            if video["id"] in exclus:
                continue
            if statut.get("privacyStatus") != "public" or not statut.get("embeddable", False):
                continue
            if contenu.get("contentRating", {}).get("ytRating") == "ytAgeRestricted":
                continue
            if duree_en_minutes(contenu.get("duration")) > DUREE_MAX_BA_MINUTES:
                continue
            if autorise_en_france(video):
                bonnes[video["id"]] = video
    return bonnes


def langue_pas_francaise(video):
    """Vrai si YouTube indique une langue audio autre que le français."""
    audio = (video.get("snippet", {}).get("defaultAudioLanguage") or "").lower()
    return bool(audio) and not audio.startswith("fr")


def bandes_annonces(films, ancien_catalogue, cle, exclus, textes_films):
    """Ajoute « bande_annonce » aux films et renvoie la mémoire des recherches.
    textes_films : {id du film: titre + description complète sur YouTube}."""
    aujourd_hui = datetime.now(timezone.utc).date()
    memoire = {fid: r for fid, r in ancien_catalogue.get("recherches_bandes_annonces", {}).items()
               if fid in films and r.get("regle") == REGLE_BA}
    # Titre corrigé depuis la dernière recherche (phrase d'accroche) : la
    # bande-annonce trouvée avec l'ancien titre ne compte plus.
    for fid in list(memoire):
        if films[fid].get("titre_accroche") and memoire[fid].get("titre") != films[fid]["titre"]:
            del memoire[fid]

    # 1. Revérifier les bandes-annonces déjà trouvées.
    deja = {fid: r["id"] for fid, r in memoire.items() if r.get("id")}
    pour_enfants = {}  # id de bande-annonce -> statut « conçu pour les enfants »
    try:
        encore_bonnes = bandes_annonces_lisibles(list(deja.values()), cle, exclus)
        for id_ba, video in encore_bonnes.items():
            pour_enfants[id_ba] = bool(video.get("status", {}).get("madeForKids", False))
        for fid, id_ba in deja.items():
            if id_ba not in encore_bonnes:
                del memoire[fid]  # supprimée ou bloquée : on cherchera une autre
    except RuntimeError as erreur:
        print(f"Vérification des bandes-annonces impossible aujourd'hui : {erreur}")

    # 2. Chercher pour les films jamais cherchés (ou sans résultat depuis longtemps).
    def a_chercher(fid):
        r = memoire.get(fid)
        if r is None:
            return True
        if r.get("id"):
            return False
        try:
            return (aujourd_hui - date.fromisoformat(r.get("date", ""))).days >= REESSAI_JOURS
        except ValueError:
            return True

    file_attente = [f for f in sorted(films.values(), key=lambda f: f["date"], reverse=True)
                    if a_chercher(f["id"])]
    candidats = {}
    for film in file_attente[:MAX_RECHERCHES]:
        try:
            candidats[film["id"]] = chercher_bande_annonce(film, cle, exclus)
        except RuntimeError as erreur:
            print(f"Recherche de bandes-annonces arrêtée (quota du jour ?) : {erreur}")
            break

    # 3. Parmi les candidates lisibles en France et en français, refuser celles
    #    d'une autre année, puis choisir dans cet ordre : VF avec preuve,
    #    VF sans preuve, VOSTFR avec preuve, VOSTFR sans preuve.
    trouvees = []
    try:
        lisibles = bandes_annonces_lisibles(
            [c[0] for liste in candidats.values() for c in liste], cle, exclus)
        for id_ba, video in lisibles.items():
            pour_enfants[id_ba] = bool(video.get("status", {}).get("madeForKids", False))
        for fid, liste in candidats.items():
            film = films[fid]
            texte_film = textes_films.get(fid) or (film["titre_youtube"] + "\n" + film["description"])
            annee_film = int(film["date"][:4]) if str(film.get("date", ""))[:4].isdigit() else None
            gardees = []
            for id_ba, titre_ba, langue in liste:
                video = lisibles.get(id_ba)
                if video is None:
                    continue
                # Une VF annoncée doit avoir un son en français. Une VOSTFR a
                # forcément un son dans une autre langue : on ne vérifie pas.
                if langue == "VF" and langue_pas_francaise(video):
                    STATS_BA["autre_langue"] += 1
                    continue
                snippet = video.get("snippet", {})
                texte_ba = snippet.get("title", "") + "\n" + snippet.get("description", "")
                verdict, detail = meme_film(texte_film, texte_ba, film["titre"], annee_film)
                if verdict == "conflit":
                    STATS_BA["conflit"] += 1
                    if len(EXEMPLES_REFUSES) < 10:
                        EXEMPLES_REFUSES.append(f"{film['titre']} → {titre_ba} ({detail})")
                    continue
                rang = (0 if langue == "VF" else 1, 0 if verdict == "preuve" else 1)
                gardees.append((rang, id_ba, titre_ba, langue, detail or "sans preuve"))
            choix, langue_choisie = None, None
            if gardees:
                rang, choix, titre_ba, langue_choisie, detail = min(gardees)
                STATS_BA["avec_preuve" if rang[1] == 0 else "sans_preuve"] += 1
                trouvees.append(f"{film['titre']} → {titre_ba} [{langue_choisie} · {detail}] "
                                f"(id : {choix})")
            memoire[fid] = {"id": choix, "langue": langue_choisie, "titre": film["titre"],
                            "date": aujourd_hui.isoformat(), "regle": REGLE_BA}
    except RuntimeError as erreur:
        print(f"Vérification des nouvelles bandes-annonces impossible : {erreur}")

    # 4. Inscrire la bande-annonce dans la fiche de chaque film.
    for fid, film in films.items():
        r = memoire.get(fid)
        if r and r.get("id"):
            film["bande_annonce"] = r["id"]
            film["bande_annonce_langue"] = r.get("langue") or "VF"  # « VF » ou « VOSTFR »
            film["bande_annonce_pour_enfants"] = pour_enfants.get(r["id"], False)
    avec = sum(1 for r in memoire.values() if r.get("id"))
    vostfr = sum(1 for r in memoire.values() if r.get("id") and r.get("langue") == "VOSTFR")
    reste = len(file_attente) - len(candidats)
    print(f"Bandes-annonces : {len(candidats)} recherches aujourd'hui, "
          f"{avec} films en ont une (dont {vostfr} en VOSTFR), {reste} films restent à chercher.")
    print(f"Refusées : {STATS_BA['pas_francais']} ni VF ni VOSTFR, {STATS_BA['autre_langue']} "
          f"« VF » mais son dans une autre langue, {STATS_BA['conflit']} d'une autre année.")
    print(f"Choisies aujourd'hui : {STATS_BA['avec_preuve']} avec preuve (même acteur ou "
          f"même année), {STATS_BA['sans_preuve']} sans preuve.")
    if trouvees:
        print("Nouvelles bandes-annonces (pour en bloquer une, ajouter son id dans exclus.txt) :")
        for ligne in trouvees:
            print("  ✓ " + ligne)
    if EXEMPLES_REFUSES:
        print("Exemples refusés (même titre, mais une autre année) :")
        for ligne in EXEMPLES_REFUSES:
            print("  ✗ " + ligne)
    return memoire


# --- Classiques du domaine public (Wikimedia Commons) -----------------------

COMMONS_API = "https://commons.wikimedia.org/w/api.php"
# Wikimedia demande que chaque robot se présente avec un nom et un contact.
USER_AGENT = "EcranLibreBot/1.0 (https://github.com/whitelion206-sudo/ecran-libre-catalogue)"


def sans_html(texte):
    return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", "", texte or "")).strip()


def infos_commons(fichiers):
    """Demande à Commons les adresses, la durée, l'image et la licence de chaque fichier."""
    infos = {}
    for debut in range(0, len(fichiers), 50):
        paquet = fichiers[debut:debut + 50]
        parametres = {
            "action": "query",
            "format": "json",
            "formatversion": "2",
            "prop": "videoinfo",
            "viprop": "url|size|mime|derivatives|extmetadata",
            "viurlwidth": "640",
            "titles": "|".join("File:" + f for f in paquet),
        }
        requete = urllib.request.Request(
            COMMONS_API + "?" + urllib.parse.urlencode(parametres),
            headers={"User-Agent": USER_AGENT},
        )
        with urllib.request.urlopen(requete, timeout=60) as reponse:
            donnees = json.load(reponse)
        requete_q = donnees.get("query", {})
        # Commons peut réécrire un nom (ex. « _ » en espace) : on garde la correspondance.
        renomme = {n["to"]: n["from"] for n in requete_q.get("normalized", [])}
        for page in requete_q.get("pages", []):
            nom = renomme.get(page["title"], page["title"])
            nom = nom[len("File:"):] if nom.startswith("File:") else nom
            if page.get("missing") or not page.get("videoinfo"):
                print(f"Classique introuvable sur Commons : {nom}")
                continue
            infos[nom.replace("_", " ")] = page["videoinfo"][0]
    return infos


def choisir_video(info):
    """Choisit une version légère pour le téléphone (environ 480p), et une de secours."""
    versions = []
    for d in info.get("derivatives", []):
        # Seules les versions réencodées par Commons (« /transcoded/ ») sont légères.
        if "webm" not in d.get("type", "") or "/transcoded/" not in d.get("src", ""):
            continue
        versions.append((int(d.get("height") or 0), "vp9" in d.get("type", ""), d["src"]))
    if not versions:
        return info.get("url", ""), info.get("url", "")
    moyennes = [v for v in versions if 300 <= v[0] <= 480]
    principale = max(moyennes or versions, key=lambda v: (v[1], v[0]))
    secours = [v for v in versions if not v[1]] or versions
    return principale[2], min(secours, key=lambda v: v[0])[2]


def fiche_classique(entree, info):
    meta = info.get("extmetadata", {})
    video, video_secours = choisir_video(info)
    duree = info.get("duration")
    return {
        "id": "commons:" + entree["fichier"],
        "titre": entree["titre"],
        "annee": entree.get("annee"),
        "realisation": entree.get("realisation", ""),
        "genre": entree.get("genre", ""),
        "genres": [entree["genre"]] if entree.get("genre") else [],
        "description": entree.get("description", ""),
        "texte_a_l_ecran": entree.get("texte_a_l_ecran", ""),
        "duree_minutes": max(1, round(duree / 60)) if duree else None,
        "video": video,
        "video_secours": video_secours,
        "miniature": info.get("thumburl", ""),
        "licence": sans_html(meta.get("LicenseShortName", {}).get("value", "")),
        "credit": sans_html(meta.get("Artist", {}).get("value", "")),
        "page_source": info.get("descriptionurl", ""),
        "source": "Wikimedia Commons",
    }


def classiques(ancien_catalogue):
    """Construit la liste des classiques. En cas de panne de Commons, garde l'ancienne liste."""
    if not os.path.exists(FICHIER_CLASSIQUES):
        return []
    with open(FICHIER_CLASSIQUES, encoding="utf-8") as f:
        entrees = json.load(f)
    try:
        infos = infos_commons([e["fichier"] for e in entrees])
    except Exception as erreur:  # Commons en panne : on ne casse pas le catalogue YouTube
        print(f"Commons indisponible ({erreur}) : je garde les classiques d'hier.")
        return ancien_catalogue.get("classiques", [])
    liste = []
    for entree in entrees:
        info = infos.get(entree["fichier"].replace("_", " "))
        if info:
            liste.append(fiche_classique(entree, info))
    print(f"Classiques : {len(liste)} sur {len(entrees)} trouvés sur Commons.")
    return liste


def lire_exclus():
    if not os.path.exists(FICHIER_EXCLUS):
        return set()
    with open(FICHIER_EXCLUS, encoding="utf-8") as f:
        lignes = (ligne.split("#")[0].strip() for ligne in f)
        return {ligne for ligne in lignes if ligne}


def main():
    cle = os.environ.get("YOUTUBE_API_KEY")
    if not cle:
        sys.exit("Il manque le secret YOUTUBE_API_KEY.")
    with open(FICHIER_CHAINES, encoding="utf-8") as f:
        chaines = json.load(f)
    exclus = lire_exclus()

    films = {}
    textes_films = {}  # titre + description complète, pour vérifier les bandes-annonces
    for chaine in chaines:
        ids = videos_de_la_chaine(chaine, cle)
        gardes = 0
        for video in details_des_videos(ids, cle):
            if not est_utilisable(video, exclus):
                continue
            if chaine.get("vf_seulement") and not est_en_francais(video):
                continue
            snippet = video.get("snippet", {})
            textes_films[video["id"]] = snippet.get("title", "") + "\n" + snippet.get("description", "")
            fiche = fiche_film(video, chaine)
            deja = films.get(video["id"])
            if deja is None or (not deja["genre"] and fiche["genre"]):
                films[video["id"]] = fiche
            gardes += 1
        print(f"{chaine['nom']} : {len(ids)} vidéos, {gardes} films gardés")

    ancien = {}
    if os.path.exists(FICHIER_CATALOGUE):
        try:
            with open(FICHIER_CATALOGUE, encoding="utf-8") as f:
                ancien = json.load(f)
        except ValueError:
            ancien = {}

    memoire_titres = vrais_titres(films, textes_films, ancien)
    films = sans_doublons(films)

    memoire_ba = bandes_annonces(films, ancien, cle, exclus, textes_films)
    liste_classiques = classiques(ancien)
    catalogue = {
        "mis_a_jour": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "nombre_de_films": len(films),
        "films": sorted(films.values(), key=lambda film: film["date"], reverse=True),
        "nombre_de_classiques": len(liste_classiques),
        "classiques": liste_classiques,
        "recherches_bandes_annonces": memoire_ba,
        "titres_trouves": memoire_titres,
    }
    with open(FICHIER_CATALOGUE, "w", encoding="utf-8") as f:
        json.dump(catalogue, f, ensure_ascii=False, indent=1)
    print(f"Catalogue écrit : {len(films)} films YouTube et {len(liste_classiques)} classiques.")
    toutes = sorted({g for film in films.values() for g in film["genres"]})
    print(f"Catégories ({len(toutes)}) : {', '.join(toutes)}")
    if GENRES_IGNORES:
        ignores = sorted(GENRES_IGNORES.items(), key=lambda x: -x[1])
        print("Genres ignorés : " + ", ".join(f"{g} ({n})" for g, n in ignores))


if __name__ == "__main__":
    main()
