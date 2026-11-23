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

Chaînes de documentaires (option « documentaires » dans chaines.json, ex. ARTE) :
- « duree_min » remplace DUREE_MIN_MINUTES (50 min pour ARTE) ;
- « titre_finit_par » : seuls les titres qui finissent par « | ARTE » sont gardés
  (les émissions, jeux et directs d'ARTE ne finissent pas comme ça) ;
- le titre est nettoyé (« | Documentaire | ARTE » enlevés, « 2/3 » gardé) et le
  genre est celui de la chaîne seulement ;
- pas de recherche de bande-annonce, ni de vrai titre sur Wikidata ;
- « import_discret » : au premier passage, les vidéos gardent leur date YouTube
  (elles n'envahissent pas les Nouveautés) ;
- « lecture_rapide » : les passages rapides ne lisent que les nouvelles vidéos et
  les vidéos déjà gardées (videos_ecartees.json retient celles déjà écartées) ;
  le grand passage du matin relit toute la chaîne.

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
from datetime import date, datetime, timedelta, timezone

API = "https://www.googleapis.com/youtube/v3/"
PAYS = "FR"
DUREE_MIN_MINUTES = 60

DOSSIER = os.path.dirname(os.path.abspath(__file__))
FICHIER_CHAINES = os.path.join(DOSSIER, "chaines.json")
FICHIER_EXCLUS = os.path.join(DOSSIER, "exclus.txt")
# Bandes-annonces vérifiées à la main : gardées même sans preuve.
FICHIER_VALIDES = os.path.join(DOSSIER, "valides.txt")
FICHIER_CATALOGUE = os.path.join(DOSSIER, "catalogue.json")
FICHIER_ECARTEES = os.path.join(DOSSIER, "videos_ecartees.json")
FICHIER_CLASSIQUES = os.path.join(DOSSIER, "classiques.json")


def appel_api(methode, parametres, cle, fatal=True):
    """Appelle l'API YouTube et renvoie la réponse JSON.

    Si fatal=False, une erreur (par exemple quota du jour épuisé) ne stoppe
    pas le robot : elle lève RuntimeError, que l'appelant peut rattraper.
    """
    parametres = dict(parametres, key=cle)
    url = API + methode + "?" + urllib.parse.urlencode(parametres)
    # Un « hoquet » passager des serveurs de YouTube (erreur 500, 503, coupure) :
    # on réessaie 2 fois avant d'abandonner. Le quota épuisé (403) n'est pas réessayé.
    for essai in range(3):
        try:
            with urllib.request.urlopen(url, timeout=30) as reponse:
                return json.load(reponse)
        except urllib.error.HTTPError as erreur:
            if erreur.code >= 500 and essai < 2:
                time.sleep(3 * (essai + 1))
                continue
            detail = erreur.read().decode("utf-8", "replace")
            message = f"Erreur de l'API YouTube ({erreur.code}) sur {methode} : {detail[:300]}"
            if fatal:
                sys.exit(message)
            raise RuntimeError(message)
        except (urllib.error.URLError, TimeoutError) as erreur:
            if essai < 2:
                time.sleep(3 * (essai + 1))
                continue
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
# « 🐎| Film Western Complet en Français », « - Film Western Complet - Acteur (1973) »,
# et aussi sans séparateur (« Guéri par l'Amour Film Complet en Français »),
# « – Téléfilm complet HD », « - Drame Complet en Français ».
FIN_DE_TITRE = re.compile(
    r"\s*(?:[|\-–—•]\s*)?\b(?:t[ée]l[ée])?(?:films?|dessins?\s+anim[ée]s?|drame|com[ée]die)\b"
    r"(?:\s+[\w'’]+){0,3}?\s+complets?\b",
    flags=re.IGNORECASE,
)
# « Traque dans la Jungle 🌀 4K » : la qualité n'est pas dans le nom du film.
QUALITE_EN_FIN = re.compile(r"\s+(?:4K|UHD|HD|ᴴᴰ)\s*$", flags=re.IGNORECASE)
# « Killer Kid 1967 », « Risen (2021) » -> l'année n'est pas dans le nom du film.
# Mais « Belfast, 1941 » (virgule) et « 2012 » (le titre entier) restent.
ANNEE_EN_FIN = re.compile(r"(?<![,\d])\s+\(?(?:19[2-9]\d|20[0-2]\d)\)?\s*$")
# « Horizons lointains | Partie 1 | Film Complet » : on garde « Partie 1 ».
PARTIE = re.compile(r"\b(partie|volume|vol\.)\s*(\d+)\b", flags=re.IGNORECASE)


def sans_emojis(texte):
    """Enlève les emojis et pictogrammes (🐎, 🥷, 😲…) d'un titre."""
    propre = "".join(c for c in texte
                     if unicodedata.category(c) not in ("So", "Sk", "Cs", "Co")
                     and c not in "‍️")
    return re.sub(r"\s+", " ", propre).strip()


def titre_propre(titre):
    """Garde seulement le nom du film, sans « Film complet… », emojis, « 4K »
    ni année à la fin."""
    morceau = FIN_DE_TITRE.split(titre)[0]
    morceau = re.split(r"\s*\|\s*", morceau)[0]
    morceau = sans_emojis(morceau).strip(" |-–—•")
    # « (Nanar) Un chalutier spatial… » : petite étiquette au début, pas dans le nom.
    morceau = re.sub(r"^[\(\[][^\)\]]{1,25}[\)\]]\s*", "", morceau)
    for _ in range(2):   # « Titre 2017 4K », « Titre 4K 2017 »
        morceau = QUALITE_EN_FIN.sub("", morceau)
        sans_annee = ANNEE_EN_FIN.sub("", morceau)
        if len(re.sub(r"\W", "", sans_annee)) >= 3:
            morceau = sans_annee
        morceau = morceau.strip(" |-–—•").rstrip(" (")
    if not morceau:
        return titre.strip()
    partie = PARTIE.search(titre)
    if partie and not PARTIE.search(morceau):
        morceau += f" – {partie.group(1).capitalize()} {partie.group(2)}"
    return morceau


SANS_NOM = []   # titres YouTube écartés faute de nom de film (affichés dans le journal)


def sans_nom_de_film(titre):
    """Vrai si le titre YouTube ne contient pas le nom du film :
    « 💥 Film d'Action Complet en Français (Jean Claude Van Damme) »,
    « Film Complet en Français - Action, SF ». Ces vidéos sont écartées."""
    debut = sans_emojis(FIN_DE_TITRE.split(titre)[0]).strip(" |-–—•")
    return not re.sub(r"\W", "", debut) and bool(FIN_DE_TITRE.search(titre))


# Titres écrits tout en majuscules (« SATANIC », « UNE SECONDE POUR MOURIR… ») :
# remis en minuscules, avec une majuscule à chaque mot important, comme les
# autres titres du catalogue. Les sigles (FBI…) et chiffres romains (II…) restent.
PETITS_MOTS = {
    "de", "du", "des", "la", "le", "les", "un", "une", "et", "à", "a", "au", "aux", "en",
    "pour", "par", "sur", "sous", "dans", "avec", "sans", "ou", "ni", "chez", "contre", "vers",
    "of", "the", "and", "in", "on", "at", "to", "for", "an",
}
SIGLES = {"FBI", "CIA", "KGB", "NYPD", "SWAT", "CSI", "USA", "UK", "URSS", "ADN", "OVNI",
          "VIP", "DJ", "NSA", "MI5", "MI6", "SOS", "TV", "NY", "SS", "OK"}
CHIFFRE_ROMAIN = re.compile(r"^(?=[IVX]{2,}$)X{0,3}(?:IX|IV|V?I{0,3})$")
ELISIONS = {"l", "d", "j", "m", "n", "s", "t", "c", "qu"}


def _mot_en_minuscules(mot, debut):
    """Un mot (sans ponctuation autour) : « L'ENTRAÎNEMENT » -> « L'Entraînement »."""
    if mot in SIGLES or CHIFFRE_ROMAIN.match(mot):
        return mot
    parties = []
    for i, partie in enumerate(mot.lower().split("-")):   # « SAINT-TROPEZ » -> « Saint-Tropez »
        m = re.match(r"^(\w+)(['’])(.+)$", partie)
        if m and m.group(1) in ELISIONS:                  # l', d', qu'…
            avant = m.group(1).capitalize() if (debut and i == 0) else m.group(1)
            parties.append(avant + m.group(2) + m.group(3)[:1].upper() + m.group(3)[1:])
        elif partie in PETITS_MOTS and not (debut and i == 0):
            parties.append(partie)
        else:
            parties.append(partie[:1].upper() + partie[1:])
    return "-".join(parties)


def _debut_en_majuscules(titre):
    """« LES CONTES DE MAUPASSANT Le Père Amable » -> « Les Contes de Maupassant –
    Le Père Amable ». Seulement quand le titre COMMENCE par au moins 3 mots tout
    en majuscules (« FBI : Mission » ou « SOS Fantômes » ne changent pas)."""
    mots = titre.split(" ")
    n = 0
    for mot in mots:
        coeur = re.sub(r"\W", "", mot)
        if len(coeur) >= 2 and coeur.isupper() and any(c.isalpha() for c in coeur):
            n += 1
        elif coeur in ("A", "À", "Y", "D", "L"):   # « À », « Y » seuls
            n += 1
        else:
            break
    if n < 3 or n == len(mots):
        return titre
    debut = sans_majuscules(" ".join(mots[:n]))
    reste = " ".join(mots[n:])
    if not re.search(r"[:–—\-|]\s*$", debut) and not re.match(r"^\s*[:–—\-|(]", reste):
        debut += " –"   # un tiret, pas « : » (sinon la règle des deux-points couperait le titre)
    return debut + " " + reste


def sans_majuscules(titre):
    """« UNE SECONDE POUR MOURIR » -> « Une Seconde pour Mourir ». Les titres qui
    ont déjà des minuscules, ou trop courts (« DJ »), ne changent pas."""
    lettres = [c for c in titre if c.isalpha()]
    if len(lettres) < 4:
        return titre
    if any(c.islower() for c in lettres):
        return _debut_en_majuscules(titre)
    resultat = []
    debut = True
    for morceau in re.split(r"(\s+)", titre):
        if not morceau or morceau.isspace():
            resultat.append(morceau)
            continue
        m = re.match(r"^(\W*)(.*?)(\W*)$", morceau)
        avant, coeur, apres = m.groups()
        resultat.append(avant + (_mot_en_minuscules(coeur, debut) if coeur else "") + apres)
        if coeur:
            debut = False
        if re.search(r"[:–—]$", morceau) or morceau in ("-", "–", "—", ":"):
            debut = True   # « FBI : MISSION » -> « FBI : Mission »
    return "".join(resultat)


MOTS_INTERDITS = re.compile(
    r"\bvost(?:fr)?\b|\bvo\b|version originale|sous[- ]titr|bande[- ]annonce|\btrailer\b|\bteaser\b"
    # Séries (« Saison 1 », « Série Complète », « Série … en entier ») : pas des films.
    r"|\bsaison\s*\d|\bs[ée]rie\s+(?:hd|tv|compl[eè]te)\b|\bs[ée]rie\b[^|]*\ben\s+entier\b"
    # Compilations de plusieurs films dans une seule vidéo.
    r"|\bcompil",
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
    # Vus le 21/11/2026 (chaînes Romances, 4K, Films TV)
    "moyen-age": "Historique", "moyen age": "Historique", "epoque": "Historique",
    "film d'epoque": "Historique", "cape et d'epee": "Aventure", "cape et epee": "Aventure",
    "dystopique": "Science-fiction", "dystopie": "Science-fiction",
    "apocalypse": "Science-fiction", "apocalyptique": "Science-fiction",
    "post-apocalyptique": "Science-fiction", "burlesque": "Comédie", "mma": "Sport",
}

# Mots qui ne sont pas des genres, à ignorer sans les noter dans le journal :
# « Thriller, Téléfilm », « Genre : Cinéma, Film en 4K, Nouveauté, Drame ».
MOTS_NEUTRES = {
    "telefilm", "telefilms", "film", "films", "cinema", "nouveaute", "nouveautes",
    "film complet", "films complets", "film entier", "film entier gratuit", "film en 4k",
    "4k", "hd", "uhd", "film en francais", "film en francais complet",
    "film cinema complet", "bonne qualite", "inedit", "exclusivite", "gratuit",
}


def est_neutre(mot):
    return sans_accents(nettoie_genre(mot)) in MOTS_NEUTRES

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


def genres_d_une_liste(texte, strict=False):
    """« Thriller, Polar / Téléfilm » -> ["Thriller", "Policier"] (mots neutres ignorés)."""
    genres = []
    for partie in re.split(r"[,/&;]|\bet\b|\s[-–]\s", texte):
        if not nettoie_genre(partie) or est_neutre(partie):
            continue
        genre = genre_normalise(partie, strict=strict)
        if genre and genre not in genres:
            genres.append(genre)
    return genres


# « Film Thriller Complet », « Film d'Action complet », « Film de Sci-Fi complet »
GENRE_DANS_FILM_COMPLET = re.compile(
    r"\b(?:t[ée]l[ée])?films?\s+(?:d['’]\s*|de\s+)?([^\W\d][\w\s'’-]{1,25}?)\s+complets?\b",
    flags=re.IGNORECASE)


def genres_du_titre(titre):
    """Lit les genres du titre YouTube : après « Film Complet en Français | »,
    entre parenthèses (« - Film complet HD (Thriller, Polar) »), ou dans
    « Film Horreur Complet »."""
    morceaux = [m.strip() for m in titre.split("|")]
    for i, morceau in enumerate(morceaux):
        if not FIN_DE_TITRE.search(morceau) and not re.search(
                r"(?:films?|dessins?\s+anim[ée]s?)\s+complets?", morceau, flags=re.IGNORECASE):
            continue
        genres = []
        dans = GENRE_DANS_FILM_COMPLET.search(morceau)
        if dans and not est_neutre(dans.group(1)):
            genres += genres_d_une_liste(dans.group(1), strict=True)
        fin = FIN_DE_TITRE.search(morceau)
        apres = morceau[fin.end():] if fin else ""
        for entre in re.findall(r"\(([^()]*)\)", apres):
            genres += genres_d_une_liste(entre)
        if i + 1 < len(morceaux):
            genres += genres_d_une_liste(morceaux[i + 1])
        genres = list(dict.fromkeys(genres))
        if genres or i + 1 < len(morceaux):
            return genres
        break
    # Genres placés ailleurs (« Accroche | Sci-Fi, Action », « Titre | Thriller, Téléfilm |
    # Film Complet ») : on prend un morceau s'il ne contient QUE des genres connus
    # (et des mots neutres comme « Téléfilm »).
    for morceau in morceaux[1:]:
        parties = [p for p in re.split(r"[,/&]|\bet\b", morceau)
                   if nettoie_genre(p) and not est_neutre(p)]
        genres = [genre_normalise(p, strict=True) for p in parties]
        if parties and all(genres):
            return list(dict.fromkeys(genres))
    return []


def genres_de_la_description(description):
    """La ligne « Genre : Cinéma, Drame, Histoire Vraie » de la description."""
    m = re.search(r"^[^\w\n]*genres?\s*:\s*(.+)$", description or "",
                  flags=re.IGNORECASE | re.MULTILINE)
    return genres_d_une_liste(m.group(1)) if m else []


# Pays francophones où l'appli pourrait être publiée. Pour chaque film, le robot
# note ceux où YouTube le bloque (« pays_bloques ») : l'appli le cache là-bas.
# La France reste obligatoire (un film bloqué en France n'est jamais gardé).
PAYS_FRANCOPHONES = {
    # Europe et Amérique du Nord
    "BE": "Belgique", "CH": "Suisse", "LU": "Luxembourg", "MC": "Monaco", "CA": "Canada",
    # Outre-mer
    "RE": "Réunion", "GP": "Guadeloupe", "MQ": "Martinique", "GF": "Guyane", "YT": "Mayotte",
    "NC": "Nouvelle-Calédonie", "PF": "Polynésie française", "PM": "Saint-Pierre-et-Miquelon",
    "BL": "Saint-Barthélemy", "MF": "Saint-Martin", "WF": "Wallis-et-Futuna",
    # Afrique et océan Indien
    "CI": "Côte d'Ivoire", "SN": "Sénégal", "CM": "Cameroun", "CD": "RD Congo", "CG": "Congo",
    "ML": "Mali", "BF": "Burkina Faso", "NE": "Niger", "BJ": "Bénin", "TG": "Togo",
    "GN": "Guinée", "GA": "Gabon", "TD": "Tchad", "CF": "Centrafrique", "BI": "Burundi",
    "RW": "Rwanda", "DJ": "Djibouti", "KM": "Comores", "MG": "Madagascar", "MU": "Maurice",
    "SC": "Seychelles", "MR": "Mauritanie", "MA": "Maroc", "DZ": "Algérie", "TN": "Tunisie",
    # Caraïbes
    "HT": "Haïti",
}


# Pays où l'appli est publiée (choisis le 23/11/2026 : presque tout le catalogue
# y est visible). Seuls ceux-là sont écrits dans le catalogue ; le journal du
# robot continue d'afficher les chiffres de tous les pays francophones.
PAYS_PUBLIES = {
    "BE", "CH", "LU", "MC",
    "GP", "MQ", "GF", "RE", "NC", "PF", "MF", "BL", "PM",
    "CI", "SN", "CM", "CD", "CG", "BJ", "TG", "GA", "GN", "CF", "RW", "BI", "MG", "MU",
    "MA", "DZ", "TN", "HT",
}
BLOQUES_TOUS = {}   # id du film -> tous les pays francophones où il est bloqué (journal)


def pays_bloques(video):
    """Pays francophones où YouTube bloque la vidéo (liste triée, vide si aucun)."""
    restriction = video.get("contentDetails", {}).get("regionRestriction", {}) or {}
    bloques = set()
    if "allowed" in restriction:
        bloques |= set(PAYS_FRANCOPHONES) - set(restriction["allowed"])
    bloques |= set(PAYS_FRANCOPHONES) & set(restriction.get("blocked", []))
    return sorted(bloques)


# --- Description courte -------------------------------------------------------------
#
# L'appli n'affiche que le résumé : on retire les liens, « Genre : … », « © … »,
# hashtags, appels à s'abonner, et on coupe proprement vers 400 caractères.
# (Le robot garde la description complète pour ses propres recherches.)
LIGNE_INUTILE = re.compile(
    r"https?://|www\.|^\W*#|©|copyright|tous droits|^\W*genres?\s*:|abonne|subscribe|"
    r"\b(?:sur|on)\s+(?:snapchat|instagram|facebook|tiktok|twitter)\b|plus de films|playlist|"
    r"^\W*(?:titre original|synopsis|r[ée]alisation|r[ée]alisateur|acteurs?|casting|avec|sc[ée]nario)\W*$|"
    r"envie de d[ée]couvrir|nous avons ce qu|^\W*films? (?:complets?|entiers?)\b[\w\s,]*$|"
    r"n'h[ée]sitez pas|commentaires|^\W*titre original\s*:|\||disponible\s+jusqu",
    flags=re.IGNORECASE)
LIMITE_DESCRIPTION = 400


def description_courte(description):
    texte = description or ""
    bloc = re.search(r"►\s*synopsis\s*:?\s*\n(.+?)(?:\n\s*►|\Z)", texte, flags=re.IGNORECASE | re.DOTALL)
    if bloc and len(bloc.group(1).strip()) >= 60:
        texte = bloc.group(1)
    lignes = [sans_emojis(l).strip(" -–—•►*") for l in texte.splitlines()]
    garde = [l for l in lignes if len(l) > 1 and not LIGNE_INUTILE.search(l)]
    texte = re.sub(r"\s+", " ", " ".join(garde)).strip()
    texte = re.sub(r"\.{2,}(?=\s|$)", ".", texte)
    # « NOUVEAUTÉ FILM ÉMOTION – film entier 2026 HD et VF : … » / « … Film Complet en Français »
    texte = re.sub(r"^[^:.!?]{0,90}\bfilms? (?:entiers?|complets?)\b[^:.!?]{0,40}:\s*", "", texte, flags=re.IGNORECASE)
    texte = re.sub(r"\s*\bfilms? (?:complets?|entiers?) en fran[çc]ais\W*$", "", texte, flags=re.IGNORECASE).strip()
    if len(texte) <= LIMITE_DESCRIPTION:
        return texte
    coupe = texte[:LIMITE_DESCRIPTION]
    fin = max(coupe.rfind(". "), coupe.rfind("! "), coupe.rfind("? "))
    if fin >= 150:
        return coupe[:fin + 1]
    return coupe[:coupe.rfind(" ")].rstrip(" ,;:") + "…"


def autorise_en_france(details):
    restriction = details.get("contentDetails", {}).get("regionRestriction", {})
    if "allowed" in restriction and PAYS not in restriction["allowed"]:
        return False
    if PAYS in restriction.get("blocked", []):
        return False
    return True


def est_utilisable(video, exclus, duree_min=DUREE_MIN_MINUTES):
    statut = video.get("status", {})
    contenu = video.get("contentDetails", {})
    if video["id"] in exclus:
        return False
    if MOTS_INTERDITS.search(video.get("snippet", {}).get("title", "")):
        return False
    if video.get("snippet", {}).get("liveBroadcastContent") in ("live", "upcoming"):
        return False
    if statut.get("privacyStatus") != "public" or not statut.get("embeddable", False):
        return False
    if contenu.get("contentRating", {}).get("ytRating") == "ytAgeRestricted":
        return False
    if duree_en_minutes(contenu.get("duration")) < duree_min:
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


def uploads_de_la_chaine(chaine, cle):
    if chaine.get("id"):
        parametres = {"part": "contentDetails", "id": chaine["id"]}
    else:
        parametres = {"part": "contentDetails", "forHandle": chaine.get("handle", "")}
    reponse = appel_api("channels", parametres, cle)
    if not reponse.get("items"):
        return None
    return reponse["items"][0]["contentDetails"]["relatedPlaylists"]["uploads"]


def nouvelles_videos(chaine, cle, connues, pages_max=10):
    """Lecture rapide : les vidéos les plus récentes d'abord, jusqu'à la
    première page qui contient une vidéo déjà connue (le reste est plus ancien)."""
    liste = uploads_de_la_chaine(chaine, cle)
    if not liste:
        return []
    nouvelles, page = [], None
    for _ in range(pages_max):
        parametres = {"part": "contentDetails", "playlistId": liste, "maxResults": 50}
        if page:
            parametres["pageToken"] = page
        reponse = appel_api("playlistItems", parametres, cle)
        ids = [item["contentDetails"]["videoId"] for item in reponse.get("items", [])]
        nouvelles += [i for i in ids if i not in connues]
        page = reponse.get("nextPageToken")
        if not page or any(i in connues for i in ids):
            break
    return nouvelles


def lire_ecartees():
    try:
        with open(FICHIER_ECARTEES, encoding="utf-8") as f:
            return {nom: set(ids) for nom, ids in json.load(f).items()}
    except (OSError, ValueError):
        return {}


def ecrire_ecartees(ecartees):
    lignes = [f"{json.dumps(nom, ensure_ascii=False)}:{json.dumps(sorted(ids))}"
              for nom, ids in sorted(ecartees.items())]
    with open(FICHIER_ECARTEES, "w", encoding="utf-8") as f:
        f.write("{\n" + ",\n".join(lignes) + "\n}\n")


# --- Documentaires (ARTE…) --------------------------------------------------------
DOCUMENTAIRES = set()   # identifiants des vidéos venues d'une chaîne « documentaires »
ETIQUETTE_DOC = re.compile(
    r"^(?:arte|documentaire|docu-?fiction|s[ée]rie documentaire|scope|reportage|arte reportage|"
    r"arte regards|doc)$", flags=re.IGNORECASE)
NUMERO_DE_PARTIE = re.compile(r"^\(?\s*(\d+)\s*/\s*(\d+)\s*\)?$")


def titre_documentaire(titre):
    """« USA, la révolution conservatrice | Nixonland (1968-1974) | 2/3 | Documentaire | ARTE »
    -> « USA, la révolution conservatrice – Nixonland (1968-1974) (2/3) »."""
    morceaux = [m.strip() for m in re.split(r"\s*\|\s*", sans_emojis(titre)) if m.strip()]
    gardes, parties = [], []
    for morceau in morceaux:
        if ETIQUETTE_DOC.match(morceau):
            continue
        numero = NUMERO_DE_PARTIE.match(morceau)
        if numero:
            parties.append(f"({numero.group(1)}/{numero.group(2)})")
            continue
        gardes.append(morceau)
    propre = " – ".join(gardes) or titre.strip()
    return " ".join([propre] + parties)


def finit_par(titre, fin):
    return bool(re.search(r"\|\s*" + re.escape(fin) + r"\s*$", titre or ""))


def details_des_videos(ids, cle):
    details = []
    for debut in range(0, len(ids), 50):
        paquet = ids[debut:debut + 50]
        # « statistics » (j'aime, vues) ne coûte rien de plus : 1 unité par appel.
        reponse = appel_api(
            "videos",
            {"part": "snippet,contentDetails,status,statistics", "id": ",".join(paquet)},
            cle,
        )
        details += reponse.get("items", [])
    return details


def titre_principal(titre):
    """« Rouge Rubis : voyageuse du temps malgré elle » -> « rouge rubis ».
    None si le titre n'a pas de sous-titre."""
    morceaux = re.split(r"\s+[:–—-]\s+", titre, maxsplit=1)
    if len(morceaux) < 2:
        return None
    principal = normalise(morceaux[0])
    return principal if len(principal) >= 4 else None


def sans_doublons(films):
    """Un même film peut être publié par plusieurs chaînes. On garde la copie
    de la chaîne qui vient en premier dans chaines.json (ou la plus ancienne),
    et on lui ajoute les genres des autres copies. Deux films de même titre
    mais de durées très différentes (un remake…) sont gardés tous les deux.
    « Rouge rubis » et « Rouge Rubis : voyageuse du temps malgré elle » sont le
    même film s'ils durent presque pareil (2 minutes d'écart au plus) ; mais
    « Harry Potter : A » et « Harry Potter : B » restent deux films."""
    gardes = {}           # titre normalisé -> fiches gardées
    par_principal = {}    # titre sans sous-titre -> fiches gardées qui ont un sous-titre
    resultat = {}
    retires = []

    def proche(a, b, ecart):
        return abs(a["duree_minutes"] - b["duree_minutes"]) <= ecart

    for fid, film in films.items():           # dans l'ordre des chaînes
        cle_titre = normalise(film["titre"])
        principal = titre_principal(film["titre"])
        double = next((a for a in gardes.get(cle_titre, []) if proche(film, a, 5)), None)
        if double is None and principal:      # « Rouge Rubis : … » après « Rouge rubis »
            double = next((a for a in gardes.get(principal, []) if proche(film, a, 2)), None)
        if double is None:                    # « Rouge rubis » après « Rouge Rubis : … »
            double = next((a for a in par_principal.get(cle_titre, []) if proche(film, a, 2)), None)
        if double is None:
            gardes.setdefault(cle_titre, []).append(film)
            if principal:
                par_principal.setdefault(principal, []).append(film)
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


# « Naufragé dans l'espace, il refuse d'être sauvé (Solis) » : une accroche,
# puis le vrai nom du film entre parenthèses.
TITRE_ENTRE_PARENTHESES = re.compile(r"^(.+?)\s*[(\[]\s*([^()\[\]]{2,40}?)\s*[)\]]\s*$")
PHRASE_AVEC_PRONOM = re.compile(r",\s*(?:il|elle|ils|elles|on)\b", flags=re.IGNORECASE)
PAS_UN_TITRE = re.compile(
    r"\b(?:vf|vostfr|version|fran[cç]ais|complet|int[ée]gral|in[ée]dit|hd|4k|"
    r"remaster|restaur|colori|director|cut|partie|[ée]pisode|saison|part)\b|^\d+$|\b(?:19|20)\d\d\b",
    flags=re.IGNORECASE,
)


def titre_entre_parentheses(titre):
    """« Naufragé dans l'espace, il refuse d'être sauvé (Solis) » -> « Solis ».
    Seulement si ce qui est avant est une vraie phrase d'accroche : « Il était
    une fois dans l'Ouest (C'era una volta il West) » garde son titre français."""
    m = TITRE_ENTRE_PARENTHESES.match(titre)
    if not m:
        return None
    avant, dedans = m.group(1).strip(" -–—,"), m.group(2).strip()
    if not 1 <= len(dedans.split()) <= 6 or PAS_UN_TITRE.search(dedans):
        return None
    phrase = (PHRASE_AVEC_PRONOM.search(avant) or VERBE_ACCROCHE.search(avant)
              or len(avant.split()) >= 9)
    if len(avant.split()) < 4 or not phrase:
        return None
    return dedans


# « Comète (Emmy Rossum, Justin Long) » : la chaîne a mis les acteurs entre
# parenthèses à la fin du titre. On les retire : « Comète ».
PARTICULES_NOMS = {"de", "du", "des", "da", "di", "van", "von", "der", "den", "le", "la",
                   "el", "al", "bin", "ben", "mc", "st", "jr", "jr."}
NOM_DE_PERSONNE = re.compile(r"^[A-ZÀ-ÖØ-Þ][\w'’.\-]*$")


def est_un_nom(texte):
    """« Emmy Rossum », « Jean-Claude Van Damme » : 2 à 4 mots à majuscule."""
    mots = texte.split()
    if not 2 <= len(mots) <= 4 or any(c.isdigit() for c in texte):
        return False
    return all(NOM_DE_PERSONNE.match(m) or m.lower() in PARTICULES_NOMS for m in mots) \
        and bool(NOM_DE_PERSONNE.match(mots[0])) and bool(NOM_DE_PERSONNE.match(mots[-1]))


def sans_acteurs_entre_parentheses(titre):
    """« Comète (Emmy Rossum, Justin Long) » -> « Comète ». Il faut au moins deux
    noms de personnes (ou « avec … ») : « Le Bon, la Brute et le Truand (Il buono,
    il brutto, il cattivo) » ne bouge pas."""
    m = re.match(r"^(.{2,}?)\s*[(\[]\s*([^()\[\]]+?)\s*[)\]]\s*$", titre)
    if not m:
        return titre
    avant, dedans = m.group(1).strip(" -–—,"), m.group(2)
    avec = re.match(r"^(?:avec|with)\s+(.+)$", dedans, flags=re.IGNORECASE)
    noms_trouves = [n.strip(" .") for n in re.split(r",|&|\set\s|\sand\s", avec.group(1) if avec else dedans)]
    noms_trouves = [n for n in noms_trouves if n]
    if not noms_trouves or not all(est_un_nom(n) for n in noms_trouves):
        return titre
    if len(noms_trouves) < 2 and not avec:
        return titre
    return avant or titre


# « (Nanar) Un chalutier spatial harponne… » : la chaîne met le genre entre
# parenthèses au début du titre. On le retire (le genre est déjà dans la fiche).
ETIQUETTE_DEBUT = re.compile(r"^\s*[(\[]\s*([^()\[\]]{2,25}?)\s*[)\]]\s*[-–—:|]?\s*(.+)$")


def sans_etiquette_de_genre(titre):
    """« (Nanar) Un chalutier spatial… » -> « Un chalutier spatial… ».
    Seulement si ce qui est entre parenthèses est un genre connu."""
    m = ETIQUETTE_DEBUT.match(titre)
    if m and len(m.group(2)) >= 2 and genre_normalise(m.group(1), strict=True):
        return m.group(2).strip()
    return titre


# « Titre original : Space Whale » dans la description : dernier recours quand
# le titre YouTube est une phrase d'accroche et que Wikidata ne connaît pas le film.
TITRE_ORIGINAL = re.compile(r"^[^\w\n]*titre\s+original\s*:\s*(.+?)\s*$",
                            flags=re.IGNORECASE | re.MULTILINE)


def titre_original(texte):
    m = TITRE_ORIGINAL.search(texte or "")
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
    genres = (genres_du_titre(snippet.get("title", "")) or genres_de_la_description(description)
              or genres_des_hashtags(description))
    genre_chaine = chaine.get("genre", "")
    if genre_chaine and genre_chaine not in genres:
        if not genres:
            genres.append(genre_chaine)
        elif genre_chaine != "Animation":
            genres.append(genre_chaine)
    fiche_titre = {}
    if chaine.get("documentaires"):
        # Documentaires : le titre YouTube est le bon, une fois nettoyé ; le genre
        # est celui de la chaîne (« Documentaire »), pas « Guerre » ou « Historique ».
        genres = [genre_chaine] if genre_chaine else []
        titre = titre_documentaire(snippet.get("title", ""))
        vrai_titre = entre_parentheses = None
    else:
        titre = sans_etiquette_de_genre(titre_propre(snippet.get("title", "")))
        vrai_titre = titre_dans_description(description)
        entre_parentheses = titre_entre_parentheses(titre)
    if vrai_titre and normalise(vrai_titre) != normalise(titre):
        # La chaîne a mis une accroche dans le titre YouTube, mais le vrai nom
        # du film dans la description : « Titre : Exeter ».
        fiche_titre = {"titre_accroche": titre}
        titre = vrai_titre
    else:
        if entre_parentheses:
            STATS_TITRES["parentheses"] += 1
            fiche_titre = {"titre_accroche": titre}
            titre = entre_parentheses
    if not chaine.get("documentaires"):
        titre = sans_acteurs_entre_parentheses(titre)
    titre = sans_majuscules(titre)
    BLOQUES_TOUS[video["id"]] = pays_bloques(video)
    return {
        **fiche_titre,
        "id": video["id"],
        "titre": titre,
        "titre_youtube": snippet.get("title", ""),
        "description": description_courte(snippet.get("description", "")),
        "duree_minutes": duree_en_minutes(video["contentDetails"].get("duration")),
        "date": snippet.get("publishedAt", ""),
        "miniature": miniature(snippet),
        "genre": genres[0] if genres else "",
        "genres": genres,
        "chaine": chaine["nom"],
        # Statut « conçu pour les enfants » de YouTube : l'appli doit couper tout
        # suivi pour ces vidéos (règles des API YouTube, III.E.4.j).
        "pour_enfants": bool(video.get("status", {}).get("madeForKids", False)),
        **statistiques(video),
        **({"pays_bloques": [c for c in pays_bloques(video) if c in PAYS_PUBLIES]}
           if any(c in PAYS_PUBLIES for c in pays_bloques(video)) else {}),
    }


def statistiques(video):
    """Nombre de vues et de « j'aime » sur YouTube. « jaime » est absent quand
    la chaîne cache ses j'aime."""
    stats = video.get("statistics", {})
    resultat = {}
    for cle_youtube, cle_catalogue in (("viewCount", "vues"), ("likeCount", "jaime")):
        valeur = str(stats.get(cle_youtube, ""))
        if valeur.isdigit():
            resultat[cle_catalogue] = int(valeur)
    return resultat


def stats_du_jour(films, ancien):
    """Les j'aime et les vues ne sont mis à jour qu'une fois par jour (premier
    passage de la journée) : sinon le catalogue changerait à chaque passage et
    l'appli le retéléchargerait pour rien. Les nouveaux films ont tout de suite
    leurs chiffres. Renvoie la date des chiffres (« statistiques_du »)."""
    aujourd_hui = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    if ancien.get("statistiques_du") != aujourd_hui:
        return aujourd_hui
    anciens = {film.get("id"): film for film in ancien.get("films", [])}
    for film in films.values():
        avant = anciens.get(film["id"])
        if avant is None or "vues" not in avant:
            continue
        for cle in ("vues", "jaime"):
            film.pop(cle, None)
            if cle in avant:
                film[cle] = avant[cle]
    return aujourd_hui


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
                "deux_points": 0, "parentheses": 0, "titre_original": 0}

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


def suite_en_minuscule(titre):
    """« Evasive Action : un convoi de détenus pris d'assaut » : après « : », une
    phrase qui commence par une minuscule décrit le film (un vrai sous-titre
    commence par une majuscule : « Astérix et Obélix : Mission Cléopâtre »)."""
    m = re.match(r"^(.{2,60}?)\s+:\s+(.+)$", titre)
    return bool(m) and m.group(2)[:1].islower()


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
        if fid in DOCUMENTAIRES:   # le titre d'un documentaire est déjà le bon
            continue
        accroche = est_une_accroche(film["titre"])
        avant = titre_avant_deux_points(film["titre"])
        if avant and (accroche or suite_en_minuscule(film["titre"])):
            # le vrai titre est déjà là, avant « : »
            STATS_TITRES["deux_points"] += 1
            film["titre_accroche"] = film["titre"]
            film["titre"] = sans_majuscules(avant)
            continue
        if not accroche:
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
        elif not film.get("titre_accroche"):
            original = titre_original(textes_films.get(fid, ""))
            if original:
                STATS_TITRES["titre_original"] += 1
                film["titre_accroche"] = film["titre"]
                film["titre"] = sans_majuscules(original)
    gardes = sum(1 for f in films.values() if f.get("titre_accroche"))
    print(f"Vrais titres : {gardes} films avec une phrase d'accroche corrigée "
          f"({STATS_TITRES['deux_points']} grâce au titre écrit avant « : », "
          f"{STATS_TITRES['parentheses']} grâce au titre écrit entre parenthèses, "
          f"{STATS_TITRES['titre_original']} grâce au « Titre original » de la description, "
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

MAX_RECHERCHES = int(os.environ.get("MAX_RECHERCHES", "60"))
# Les passages rapides de la journée (toutes les 4 heures) mettent 0 : ils
# ajoutent les nouveaux films sans toucher au quota de recherche, gardé pour
# le grand passage du matin.
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
REGLE_BA = 6   # (règle 7 « preuve obligatoire » : appliquée sans tout effacer, voir bandes_annonces)
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
            "sans_preuve": 0, "sans_indice": 0, "retirees": []}
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


def a_des_indices(texte_film, titre_film, annee_mise_en_ligne):
    """Vrai si la description du film donne de quoi prouver qu'une
    bande-annonce est la bonne : un nom (acteur, réalisateur) ou une année."""
    annees, noms = preuves(texte_film, set(normalise(titre_film).split()))
    if annee_mise_en_ligne:
        annees = {a for a in annees if int(a) < annee_mise_en_ligne}
    return bool(annees or noms)


def bandes_annonces(films, ancien_catalogue, cle, exclus, textes_films, valides=frozenset()):
    """Ajoute « bande_annonce » aux films et renvoie la mémoire des recherches.
    textes_films : {id du film: titre + description complète sur YouTube}.
    Règle 7 : une bande-annonce n'est choisie qu'avec une preuve (même acteur
    ou même année que le film), sauf si elle figure dans valides.txt."""
    aujourd_hui = datetime.now(timezone.utc).date()
    titres_valides = {normalise(v) for v in valides}

    def texte_et_annee(film):
        texte = textes_films.get(film["id"]) or (film["titre_youtube"] + "\n" + film["description"])
        annee = int(film["date"][:4]) if str(film.get("date", ""))[:4].isdigit() else None
        return texte, annee

    def est_valide(film, id_ba):
        return id_ba in valides or normalise(film["titre"]) in titres_valides
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
                continue
            # Choisie autrefois sans preuve : on la retire, sauf si elle a été
            # vérifiée à la main (valides.txt).
            film = films[fid]
            if est_valide(film, id_ba):
                continue
            snippet = encore_bonnes[id_ba].get("snippet", {})
            texte_ba = snippet.get("title", "") + "\n" + snippet.get("description", "")
            texte_film, annee_film = texte_et_annee(film)
            verdict, _ = meme_film(texte_film, texte_ba, film["titre"], annee_film)
            if verdict != "preuve":
                STATS_BA["retirees"].append(f"{film['titre']} (id : {id_ba})")
                memoire[fid] = {"id": None, "titre": film["titre"],
                                "date": aujourd_hui.isoformat(), "regle": REGLE_BA}
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

    # Inutile de chercher (et de dépenser du quota) pour un film dont la
    # description ne donne ni acteur ni année : on ne pourrait rien prouver.
    file_attente = []
    for f in sorted(films.values(), key=lambda f: f["date"], reverse=True):
        if f["id"] in DOCUMENTAIRES or not a_chercher(f["id"]):
            continue
        texte_film, annee_film = texte_et_annee(f)
        if a_des_indices(texte_film, f["titre"], annee_film) or normalise(f["titre"]) in titres_valides:
            file_attente.append(f)
        else:
            STATS_BA["sans_indice"] += 1
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
            texte_film, annee_film = texte_et_annee(film)
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
                if verdict != "preuve" and not est_valide(film, id_ba):
                    STATS_BA["sans_preuve"] += 1  # même titre, mais rien ne prouve que c'est le même film
                    continue
                rang = (0 if langue == "VF" else 1, 0 if verdict == "preuve" else 1)
                gardees.append((rang, id_ba, titre_ba, langue, detail or "vérifiée à la main"))
            choix, langue_choisie = None, None
            if gardees:
                rang, choix, titre_ba, langue_choisie, detail = min(gardees)
                STATS_BA["avec_preuve"] += 1
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
          f"« VF » mais son dans une autre langue, {STATS_BA['conflit']} d'une autre année, "
          f"{STATS_BA['sans_preuve']} sans preuve que c'est le même film.")
    print(f"Choisies aujourd'hui : {STATS_BA['avec_preuve']} (même acteur ou même année). "
          f"Films non cherchés faute d'indice (ni acteur ni année) : {STATS_BA['sans_indice']}.")
    if STATS_BA["retirees"]:
        print(f"Retirées car choisies sans preuve : {len(STATS_BA['retirees'])} "
              f"(ex. : {', '.join(STATS_BA['retirees'][:6])})")
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


def lire_liste(chemin):
    """Une valeur par ligne ; ce qui suit « # » est un commentaire."""
    if not os.path.exists(chemin):
        return set()
    with open(chemin, encoding="utf-8") as f:
        lignes = (ligne.split("#")[0].strip() for ligne in f)
        return {ligne for ligne in lignes if ligne}


def lire_exclus():
    return lire_liste(FICHIER_EXCLUS)


def lire_valides():
    """valides.txt : titres de films (comme dans l'appli) ou ids de
    bandes-annonces vérifiées à la main."""
    return lire_liste(FICHIER_VALIDES)


# --- Date d'arrivée dans l'appli ----------------------------------------------
#
# « date » est la date de mise en ligne sur YouTube. « ajoute_le » est le jour
# où le film est entré dans Écran Libre : c'est elle que l'appli utilise pour
# la rangée « Nouveautés ». Un vieux film d'une chaîne qu'on vient d'ajouter
# apparaît ainsi comme nouveau.
#
# Premier passage avec cette règle : les films déjà présents reçoivent leur date
# YouTube (rien ne bouge), sauf ceux des chaînes ajoutées le 20 novembre 2026,
# qui comptent comme arrivés ce soir-là.
CHAINES_AJOUTEES_LE_20_NOVEMBRE = {
    "Boxoffice | ROMANCES | Films Complets",
    "Boxoffice | 4K | Films Complets",
    "Boxoffice | Films TV",
}
SOIREE_DU_20_NOVEMBRE = "2026-11-20T19:20:00Z"


def dates_d_ajout(films, ancien, discretes=()):
    """Donne à chaque film sa date « ajoute_le ». Renvoie le nombre de films
    arrivés à ce passage. Chaîne « import_discret » qui arrive pour la première
    fois (aucun de ses films dans l'ancien catalogue) : ses vidéos gardent leur
    date YouTube, pour ne pas envahir les Nouveautés."""
    maintenant = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:00Z")
    anciens = {film.get("id"): film for film in ancien.get("films", [])}
    chaines_connues = {film.get("chaine") for film in anciens.values()}
    premiere_fois = {c for c in discretes if c not in chaines_connues} if anciens else set()
    # Même film gardé sous une autre copie (doublon) : on le retrouve par son titre.
    par_titre = {}
    for film in anciens.values():
        if film.get("ajoute_le"):
            par_titre.setdefault(normalise(film.get("titre", "")), []).append(film)
    nouveaux = 0
    for film in films.values():
        avant = anciens.get(film["id"])
        if avant is not None:
            if avant.get("ajoute_le"):
                film["ajoute_le"] = avant["ajoute_le"]
            elif avant.get("chaine") in CHAINES_AJOUTEES_LE_20_NOVEMBRE:
                film["ajoute_le"] = SOIREE_DU_20_NOVEMBRE
            else:
                film["ajoute_le"] = film.get("date") or maintenant
            continue
        meme = next((a for a in par_titre.get(normalise(film["titre"]), [])
                     if abs((a.get("duree_minutes") or 0) - film["duree_minutes"]) <= 5), None)
        if meme is not None:
            film["ajoute_le"] = meme["ajoute_le"]
            continue
        if film.get("chaine") in premiere_fois:
            film["ajoute_le"] = film.get("date") or maintenant
            continue
        film["ajoute_le"] = maintenant
        nouveaux += 1
    return nouveaux


# --- Tendances de la semaine ----------------------------------------------------
#
# Chaque jour, le robot note les vues YouTube de chaque film dans
# historique_vues.json (8 derniers jours, un jour par ligne). Il compare avec
# il y a 7 jours : les 20 films qui ont gagné le plus de vues reçoivent
# « tendance » (rang 1 à 20) et « vues_7j » (vues gagnées). Un film publié sur
# YouTube pendant la semaine compte toutes ses vues. Pas encore 7 jours
# d'historique : pas de tendances (l'appli cache la rangée).
FICHIER_HISTORIQUE = os.path.join(DOSSIER, "historique_vues.json")
JOURS_TENDANCE = 7
TAILLE_TENDANCES = 20


def lire_historique():
    try:
        with open(FICHIER_HISTORIQUE, encoding="utf-8") as f:
            return json.load(f).get("jours", {})
    except (OSError, ValueError):
        return {}


def ecrire_historique(jours):
    lignes = [f"{json.dumps(d)}:{json.dumps(jours[d], separators=(',', ':'), sort_keys=True)}"
              for d in sorted(jours)]
    with open(FICHIER_HISTORIQUE, "w", encoding="utf-8") as f:
        f.write('{"jours":{\n' + ",\n".join(lignes) + "\n}}\n")


def tendances(films, aujourd_hui, jours=None):
    """Note les vues du jour, puis classe les films qui en gagnent le plus en 7 jours.
    Renvoie le nombre de films classés (0 si l'historique est trop court)."""
    if jours is None:
        jours = lire_historique()
    du_jour = dict(jours.get(aujourd_hui, {}))
    for film in films.values():
        if isinstance(film.get("vues"), int):
            du_jour[film["id"]] = film["vues"]
    jours[aujourd_hui] = du_jour
    jour = datetime.strptime(aujourd_hui, "%Y-%m-%d")
    garder_depuis = (jour - timedelta(days=JOURS_TENDANCE + 1)).strftime("%Y-%m-%d")
    for d in [d for d in jours if d < garder_depuis]:
        del jours[d]
    ecrire_historique(jours)

    reference = (jour - timedelta(days=JOURS_TENDANCE)).strftime("%Y-%m-%d")
    candidates = [d for d in jours if d <= reference]
    if not candidates:
        return 0
    jour_base = max(candidates)
    base = jours[jour_base]
    gains = []
    for film in films.values():
        vues = film.get("vues")
        if not isinstance(vues, int):
            continue
        if film["id"] in base:
            gain = vues - base[film["id"]]
        elif film.get("date", "")[:10] > jour_base:
            gain = vues          # publié sur YouTube pendant la semaine
        else:
            continue             # arrivé dans l'appli trop récemment pour comparer
        if gain > 0:
            gains.append((gain, film))
    gains.sort(key=lambda g: (-g[0], g[1]["id"]))
    for rang, (gain, film) in enumerate(gains[:TAILLE_TENDANCES], 1):
        film["tendance"] = rang
        film["vues_7j"] = gain
    return min(len(gains), TAILLE_TENDANCES)


# --- Corrections à la main --------------------------------------------------------
#
# corrections.txt (à la racine du dépôt), une correction par ligne :
#     titre actuel dans l'appli => bon titre
#     titre actuel dans l'appli => bon titre | Genre1, Genre2
# Les lignes qui commencent par # sont ignorées. On peut aussi mettre
# l'identifiant YouTube du film à gauche. Majuscules et accents ne comptent pas.
FICHIER_CORRECTIONS = os.path.join(DOSSIER, "corrections.txt")


CORRIGES = set()   # films touchés par corrections.txt (pas besoin de les relister)


def lire_corrections():
    corrections = []
    try:
        with open(FICHIER_CORRECTIONS, encoding="utf-8") as f:
            lignes = f.read().splitlines()
    except OSError:
        return corrections
    for ligne in lignes:
        ligne = ligne.strip()
        if not ligne or ligne.startswith("#") or "=>" not in ligne:
            continue
        gauche, droite = (x.strip() for x in ligne.split("=>", 1))
        titre, _, genres = (x.strip() for x in droite.partition("|"))
        if gauche and (titre or genres):
            corrections.append((gauche, titre, genres))
    return corrections


def appliquer_corrections(films, corrections=None):
    """Applique corrections.txt. Renvoie (nombre de films corrigés, lignes sans film).
    Les identifiants des films corrigés sont ajoutés à CORRIGES."""
    if corrections is None:
        corrections = lire_corrections()
    index = {}
    for film in films.values():
        for cle in (film["id"], normalise(film["titre"]), normalise(film.get("titre_youtube", ""))):
            if cle:
                index.setdefault(cle, []).append(film)
    corriges, sans_film = 0, []
    for gauche, titre, genres in corrections:
        cibles = index.get(gauche) or index.get(normalise(gauche)) or []
        if not cibles:
            sans_film.append(gauche)
            continue
        liste = []
        for g in re.split(r"[,/]", genres):
            g = genre_normalise(g, strict=True) if nettoie_genre(g) else None
            if g and g not in liste:
                liste.append(g)
        for film in cibles:
            CORRIGES.add(film["id"])
            if titre:
                film["titre"] = titre
            if liste:
                film["genres"] = liste
                film["genre"] = liste[0]
            corriges += 1
    return corriges, sans_film


# --- Liste des titres à corriger ---------------------------------------------------
#
# a_corriger.txt : les films dont le titre est encore une phrase d'accroche (le
# robot n'a pas trouvé le vrai titre), déjà au format de corrections.txt. Il suffit
# de copier la ligne dans corrections.txt et d'écrire le vrai titre après « => ».
FICHIER_A_CORRIGER = os.path.join(DOSSIER, "a_corriger.txt")


def ecrire_a_corriger(films, memoire_titres):
    liste = [f for fid, f in films.items()
             if fid in memoire_titres and not (memoire_titres[fid] or {}).get("titre")
             and fid not in CORRIGES]
    lignes = [
        "# Films dont le titre est encore une phrase d'accroche (mis à jour par le robot).",
        "# Pour en corriger un : copie sa ligne dans corrections.txt et écris le vrai titre après « => ».",
        "# Si le titre est déjà le bon, recopie-le après « => » : il ne sera plus listé ici.",
        f"# {len(liste)} film(s).",
        "",
    ]
    for f in sorted(liste, key=lambda f: (f.get("chaine", ""), f["titre"].lower())):
        m = f.get("duree_minutes") or 0
        duree = f"{m // 60} h {m % 60:02d}" if m >= 60 else f"{m} min"
        lignes.append(f"# {f.get('chaine', '')} · {duree} · https://www.youtube.com/watch?v={f['id']}")
        lignes.append(f"{f['titre']} => ")
        lignes.append("")
    with open(FICHIER_A_CORRIGER, "w", encoding="utf-8") as fichier:
        fichier.write("\n".join(lignes))
    return len(liste)


def main():
    cle = os.environ.get("YOUTUBE_API_KEY")
    if not cle:
        sys.exit("Il manque le secret YOUTUBE_API_KEY.")
    with open(FICHIER_CHAINES, encoding="utf-8") as f:
        chaines = json.load(f)
    exclus = lire_exclus()

    ancien = {}
    if os.path.exists(FICHIER_CATALOGUE):
        try:
            with open(FICHIER_CATALOGUE, encoding="utf-8") as f:
                ancien = json.load(f)
        except ValueError:
            ancien = {}
    ecartees_avant = lire_ecartees()
    ecartees = {}
    lecture_complete = MAX_RECHERCHES > 0   # grand passage du matin et lancements à la main

    films = {}
    textes_films = {}  # titre + description complète, pour vérifier les bandes-annonces
    for chaine in chaines:
        nom = chaine["nom"]
        rapide = chaine.get("lecture_rapide") and not lecture_complete and nom in ecartees_avant
        if rapide:
            deja_gardes = [f["id"] for f in ancien.get("films", []) if f.get("chaine") == nom]
            connues = set(deja_gardes) | ecartees_avant[nom]
            ids = list(dict.fromkeys(nouvelles_videos(chaine, cle, connues) + deja_gardes))
            ecartees[nom] = set(ecartees_avant[nom])
        else:
            ids = videos_de_la_chaine(chaine, cle)
            if chaine.get("lecture_rapide"):
                ecartees[nom] = set()
        duree_min = chaine.get("duree_min", DUREE_MIN_MINUTES)
        gardes = 0
        for video in details_des_videos(ids, cle):
            snippet = video.get("snippet", {})
            titre_yt = snippet.get("title", "")
            ok = est_utilisable(video, exclus, duree_min)
            if ok and chaine.get("vf_seulement") and not est_en_francais(video):
                ok = False
            if ok and chaine.get("titre_finit_par") and not finit_par(titre_yt, chaine["titre_finit_par"]):
                ok = False
            if ok and sans_nom_de_film(titre_yt):
                SANS_NOM.append(titre_yt)
                ok = False
            if not ok:
                if nom in ecartees:
                    ecartees[nom].add(video["id"])
                continue
            if nom in ecartees:
                ecartees[nom].discard(video["id"])
            if chaine.get("documentaires"):
                DOCUMENTAIRES.add(video["id"])
            textes_films[video["id"]] = titre_yt + "\n" + snippet.get("description", "")
            fiche = fiche_film(video, chaine)
            deja = films.get(video["id"])
            if deja is None or (not deja["genre"] and fiche["genre"]):
                films[video["id"]] = fiche
            gardes += 1
        print(f"{nom} : {len(ids)} vidéos lues{' (lecture rapide)' if rapide else ''}, {gardes} films gardés")
    if ecartees:
        ecrire_ecartees(ecartees)

    memoire_titres = vrais_titres(films, textes_films, ancien)
    corriges, sans_film = appliquer_corrections(films)
    if corriges or sans_film:
        print(f"Corrections à la main : {corriges} films corrigés"
              + (f" ; introuvables : {' ; '.join(sans_film)}" if sans_film else "."))
    films = sans_doublons(films)
    print(f"Titres encore à corriger (voir a_corriger.txt) : {ecrire_a_corriger(films, memoire_titres)}.")

    memoire_ba = bandes_annonces(films, ancien, cle, exclus, textes_films, lire_valides())
    date_stats = stats_du_jour(films, ancien)
    arrives = dates_d_ajout(films, ancien, {c["nom"] for c in chaines if c.get("import_discret")})
    print(f"Arrivés dans l'appli à ce passage : {arrives} films.")
    nb_tendances = tendances(films, date_stats)
    print(f"Tendances de la semaine : {nb_tendances} films classés"
          + ("." if nb_tendances else " (il faut 7 jours d'historique des vues)."))
    liste_classiques = classiques(ancien)
    catalogue = {
        "mis_a_jour": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "nombre_de_films": len(films),
        "films": sorted(films.values(), key=lambda film: film["date"], reverse=True),
        "nombre_de_classiques": len(liste_classiques),
        "classiques": liste_classiques,
        "recherches_bandes_annonces": memoire_ba,
        "titres_trouves": memoire_titres,
        "statistiques_du": date_stats,
    }
    # Rien de nouveau depuis le dernier passage : on garde l'ancienne date, pour
    # que le fichier ne change pas. L'appli voit alors qu'il n'y a rien à
    # retélécharger (pas de données mobiles gaspillées).
    sans_date = lambda c: {k: v for k, v in c.items() if k != "mis_a_jour"}
    if ancien.get("mis_a_jour") and sans_date(ancien) == json.loads(json.dumps(sans_date(catalogue))):
        catalogue["mis_a_jour"] = ancien["mis_a_jour"]
        print("Aucun changement depuis le dernier passage : catalogue identique.")
    with open(FICHIER_CATALOGUE, "w", encoding="utf-8") as f:
        json.dump(catalogue, f, ensure_ascii=False, separators=(",", ":"))
    print(f"Catalogue écrit : {len(films)} films YouTube et {len(liste_classiques)} classiques.")
    if SANS_NOM:
        print(f"Écartés car le titre YouTube ne donne pas le nom du film : {len(SANS_NOM)} "
              f"(ex. : {' ; '.join(SANS_NOM[:3])})")
    if films:
        bloques = {fid: BLOQUES_TOUS.get(fid, f.get("pays_bloques", [])) for fid, f in films.items()}
        par_pays = sorted(((sum(1 for fid in films if code not in bloques[fid]), code)
                           for code in PAYS_FRANCOPHONES), key=lambda x: (-x[0], x[1]))
        bloques_partout = sum(1 for fid in films if bloques[fid])
        print(f"Films visibles par pays (sur {len(films)}, dont {bloques_partout} bloqués dans au moins un pays) :")
        print("  " + " · ".join(f"{PAYS_FRANCOPHONES[c]} {n}" for n, c in par_pays))
    toutes = sorted({g for film in films.values() for g in film["genres"]})
    print(f"Catégories ({len(toutes)}) : {', '.join(toutes)}")
    if GENRES_IGNORES:
        ignores = sorted(GENRES_IGNORES.items(), key=lambda x: -x[1])
        print("Genres ignorés : " + ", ".join(f"{g} ({n})" for g, n in ignores))


if __name__ == "__main__":
    main()
