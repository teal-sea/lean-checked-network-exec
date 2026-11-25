#!/usr/bin/env python3
"""Generate python/bytelm/corpus.txt: the training corpus for the tiny byte LM.

Deterministic (fixed seed, no external input). ~220 KB of short, plain ASCII
English lines, chosen so 32-byte causal windows see whole sentence patterns:

- factual one-liners (capitals, simple arithmetic in words, days, months)
- classic public-domain proverbs and aphorisms
- formal-verification Q&A lines in the engine's own vocabulary
- short micro-dialogs
- templated everyday sentences with common words
- letter-by-letter spelling lines for the factual words

Run:  python3 make_corpus.py   (writes corpus.txt next to this file)
"""

import random
from pathlib import Path

OUT = Path(__file__).resolve().parent / "corpus.txt"

# ---------------------------------------------------------------- factual content

CAPITALS = [
    ("France", "Paris"), ("Germany", "Berlin"), ("Italy", "Rome"), ("Spain", "Madrid"),
    ("Portugal", "Lisbon"), ("England", "London"), ("Scotland", "Edinburgh"),
    ("Ireland", "Dublin"), ("Greece", "Athens"), ("Norway", "Oslo"),
    ("Sweden", "Stockholm"), ("Denmark", "Copenhagen"), ("Finland", "Helsinki"),
    ("Poland", "Warsaw"), ("Austria", "Vienna"), ("Switzerland", "Bern"),
    ("Netherlands", "Amsterdam"), ("Belgium", "Brussels"), ("Japan", "Tokyo"),
    ("China", "Beijing"), ("India", "New Delhi"), ("Egypt", "Cairo"),
    ("Kenya", "Nairobi"), ("Morocco", "Rabat"), ("Brazil", "Brasilia"),
    ("Peru", "Lima"), ("Chile", "Santiago"), ("Canada", "Ottawa"),
    ("Mexico", "Mexico City"), ("Australia", "Canberra"), ("Russia", "Moscow"),
    ("Turkey", "Ankara"), ("Vietnam", "Hanoi"), ("Thailand", "Bangkok"),
    ("Korea", "Seoul"), ("Iceland", "Reykjavik"), ("Cuba", "Havana"),
    ("Iraq", "Baghdad"), ("Iran", "Tehran"), ("Jordan", "Amman"),
    ("Wales", "Cardiff"), ("Hungary", "Budapest"), ("Romania", "Bucharest"),
    ("Bulgaria", "Sofia"), ("Serbia", "Belgrade"), ("Ukraine", "Kyiv"),
    ("Nigeria", "Abuja"), ("Ghana", "Accra"), ("Senegal", "Dakar"),
    ("Ethiopia", "Addis Ababa"), ("Tanzania", "Dodoma"), ("Argentina", "Buenos Aires"),
    ("Colombia", "Bogota"), ("Ecuador", "Quito"), ("Bolivia", "Sucre"),
    ("Venezuela", "Caracas"), ("Uruguay", "Montevideo"), ("Panama", "Panama City"),
]

NUMBERS = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight",
           "nine", "ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen",
           "sixteen", "seventeen", "eighteen", "nineteen", "twenty"]

DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
MONTHS = ["January", "February", "March", "April", "May", "June", "July",
          "August", "September", "October", "November", "December"]

PROVERBS = [
    "A stitch in time saves nine.",
    "Actions speak louder than words.",
    "All that glitters is not gold.",
    "An apple a day keeps the doctor away.",
    "Better late than never.",
    "Birds of a feather flock together.",
    "Cleanliness is next to godliness.",
    "Don't count your chickens before they hatch.",
    "Don't judge a book by its cover.",
    "Early to bed and early to rise makes a man healthy, wealthy, and wise.",
    "Every cloud has a silver lining.",
    "Fortune favors the bold.",
    "Haste makes waste.",
    "He who laughs last laughs longest.",
    "If it ain't broke, don't fix it.",
    "Ignorance is bliss.",
    "It takes two to tango.",
    "Knowledge is power.",
    "Laughter is the best medicine.",
    "Let sleeping dogs lie.",
    "Look before you leap.",
    "Necessity is the mother of invention.",
    "No man is an island.",
    "Old habits die hard.",
    "Once bitten, twice shy.",
    "Practice makes perfect.",
    "Rome was not built in a day.",
    "Slow and steady wins the race.",
    "Still waters run deep.",
    "Strike while the iron is hot.",
    "The early bird catches the worm.",
    "The pen is mightier than the sword.",
    "Time heals all wounds.",
    "Time and tide wait for no man.",
    "Two heads are better than one.",
    "Variety is the spice of life.",
    "When in Rome, do as the Romans do.",
    "Where there is smoke there is fire.",
    "You cannot make an omelet without breaking eggs.",
    "You reap what you sow.",
    "A journey of a thousand miles begins with a single step.",
    "A picture is worth a thousand words.",
    "Absence makes the heart grow fonder.",
    "Barking dogs seldom bite.",
    "Beauty is only skin deep.",
    "Blood is thicker than water.",
    "Curiosity killed the cat.",
    "Do unto others as you would have them do unto you.",
    "Easy come, easy go.",
    "Every dog has its day.",
    "Great minds think alike.",
    "Honesty is the best policy.",
    "If the shoe fits, wear it.",
    "Imitation is the sincerest form of flattery.",
    "It is no use crying over spilt milk.",
    "Kill two birds with one stone.",
    "Money does not grow on trees.",
    "Never bite the hand that feeds you.",
    "Nothing ventured, nothing gained.",
    "One swallow does not make a summer.",
    "Out of sight, out of mind.",
    "Patience is a virtue.",
    "People who live in glass houses should not throw stones.",
    "Prevention is better than cure.",
    "The grass is always greener on the other side.",
    "There is no place like home.",
    "Too many cooks spoil the broth.",
    "When the cat is away, the mice will play.",
    "A friend in need is a friend indeed.",
    "A watched pot never boils.",
    "As you make your bed, so you must lie in it.",
    "Half a loaf is better than none.",
]

# ---------------------------------------------------------------- verification vocabulary

VERIFY_QA = [
    ("What does the engine check?", "The engine checks every proof step."),
    ("What does load_check do?", "It checks that every weight is in range."),
    ("What does forward_logits return?", "It returns the logits for the last position."),
    ("What does predict_next do?", "It picks the largest logit."),
    ("What is a proof?", "A proof is a chain of steps."),
    ("What is a lemma?", "A lemma is a helper proof."),
    ("What is a theorem?", "A theorem is a proved statement."),
    ("What is a kernel?", "A kernel is a small verified core."),
    ("What is an invariant?", "An invariant is a property that always holds."),
    ("What is a bound?", "A bound is a limit on a value."),
    ("What is a fixed point?", "A fixed point is a number with a fixed scale."),
    ("What is the residual stream?", "It is the sum of the parts each layer adds."),
    ("What is attention?", "Attention mixes earlier positions into the current one."),
    ("What is the softmax?", "The softmax turns scores into weights."),
    ("What is the unembedding?", "The unembedding maps the stream to logits."),
    ("What is quantization?", "Quantization turns real weights into integers."),
    ("What is a byte model?", "A byte model predicts the next byte of text."),
    ("What is greedy decoding?", "Greedy decoding always takes the best token."),
    ("What is a prompt?", "A prompt is the start of the text."),
    ("What is a completion?", "A completion is what the model adds to the prompt."),
    ("Why use integers?", "Integers are exact on every machine."),
    ("Why check for overflow?", "Overflow would wrap and give a wrong answer."),
    ("What is a causal mask?", "A causal mask hides the future from the past."),
    ("What is a table?", "A table stores values that are ready to read."),
    ("What is rounding?", "Rounding picks the nearest integer."),
    ("What is truncation?", "Truncation drops the part after the point."),
    ("Is the engine exact?", "Yes, the engine is exact."),
    "The proof checks each step of the program.",
    "The engine reads the same bytes in every language.",
    "The weights are integers, so the model is exact.",
    "The scales are powers of two, so the shifts are exact.",
    "A proof is checked step by step, and every step must hold.",
    "The engine, the Python reference, and the browser agree bit for bit.",
]

DIALOGS = [
    "Hello. Hello, how are you? I am fine, thank you.",
    "Good morning. Good morning to you too.",
    "What is your name? My name is Sam.",
    "How is the weather? The weather is fine today.",
    "Where are you going? I am going to the market.",
    "Would you like some tea? Yes, please, with milk.",
    "Thank you very much. You are most welcome.",
    "See you tomorrow. Goodbye, take care.",
    "Can I help you? Yes, I am looking for a book.",
    "How old is the house? The house is very old.",
    "What time is it? It is almost noon.",
    "Is the store open? Yes, it is open until six.",
    "Do you like music? Yes, I like quiet music.",
    "Where do you live? I live near the river.",
    "What do you do? I work with numbers and proofs.",
    "Please pass the salt. Here you are.",
    "How was your day? My day was long but good.",
    "Are you coming with us? Yes, I will come along.",
]

# ---------------------------------------------------------------- templated everyday English

ADJ = ["small", "large", "old", "new", "quiet", "bright", "cold", "warm",
       "happy", "busy", "simple", "clean", "long", "short", "green", "red",
       "strong", "gentle", "kind", "swift"]
NOUN = ["cat", "dog", "bird", "horse", "child", "teacher", "farmer", "book",
        "letter", "table", "garden", "river", "road", "house", "engine", "proof",
        "number", "table", "morning", "evening", "winter", "summer", "letter", "song"]
VERB = ["saw", "found", "read", "wrote", "kept", "took", "gave", "held",
        "opened", "closed", "watched", "carried", "checked", "proved", "knew", "loved"]
PLACE = ["in the garden", "on the table", "by the river", "near the road",
         "in the house", "under the tree", "after the rain", "before the storm",
         "during the winter", "beside the wall"]

def everyday(rng):
    a, n1, v, n2 = rng.choice(ADJ), rng.choice(NOUN), rng.choice(VERB), rng.choice(NOUN)
    patterns = [
        f"The {a} {n1} {v} the {n2}.",
        f"A {a} {n1} {v} the {n2} {rng.choice(PLACE)}.",
        f"The {n1} {v} the {a} {n2} {rng.choice(PLACE)}.",
        f"Every {n1} {v} a {n2}.",
        f"My {a} {n1} {v} your {n2}.",
        f"The {n1} and the {n2} {v} the {a} one.",
    ]
    return rng.choice(patterns)

SPELL = {
    "Paris": "P a r i s", "London": "L o n d o n", "Rome": "R o m e",
    "Tokyo": "T o k y o", "Berlin": "B e r l i n", "Madrid": "M a d r i d",
    "Vienna": "V i e n n a", "Oslo": "O s l o", "Athens": "A t h e n s",
    "Cairo": "C a i r o", "engine": "e n g i n e", "proof": "p r o o f",
    "weight": "w e i g h t", "number": "n u m b e r", "letter": "l e t t e r",
    "morning": "m o r n i n g", "evening": "e v e n i n g", "garden": "g a r d e n",
    "river": "r i v e r", "winter": "w i n t e r", "summer": "s u m m e r",
}

# ---------------------------------------------------------------- assembly


def main():
    rng = random.Random(4217)
    lines = []

    def add(s):
        lines.append(s)

    # capitals, three phrasings plus spelling
    for country, capital in CAPITALS:
        add(f"The capital of {country} is {capital}.")
        add(f"{capital} is the capital of {country}.")
        add(f"Do you know the capital of {country}? It is {capital}.")
    for word, spell in SPELL.items():
        add(f"{word} is spelled {spell}.")

    # arithmetic in words (results stay within the word list, zero to twenty)
    for i in range(21):
        for j in range(21 - i):
            add(f"{NUMBERS[i]} plus {NUMBERS[j]} is {NUMBERS[i + j]}.")
            if i >= j and NUMBERS[i] != "zero":
                d = i - j
                add(f"{NUMBERS[i]} minus {NUMBERS[j]} is {NUMBERS[d]}.")

    # calendar facts
    for d in DAYS:
        add(f"{d} is a day of the week.")
        add(f"On {d} the shop opens early.")
    for m in MONTHS:
        add(f"{m} is a month of the year.")
        add(f"In {m} the days grow longer.")

    # proverbs, several passes for crisp memorization
    for _ in range(6):
        for p in PROVERBS:
            add(p)

    # verification Q&A and prose
    for _ in range(3):
        for item in VERIFY_QA:
            if isinstance(item, tuple):
                add(f"{item[0]} {item[1]}")
            else:
                add(item)

    # dialogs
    for _ in range(3):
        for d in DIALOGS:
            add(d)

    # templated everyday sentences (grammar practice, deliberately a minority:
    # random word fills are unpredictable, so they set a floor on entropy)
    for _ in range(900):
        add(everyday(rng))

    # short question-and-answer lines over the same vocabulary
    for _ in range(300):
        n1, n2 = rng.choice(NOUN), rng.choice(NOUN)
        a = rng.choice(ADJ)
        add(rng.choice([
            f"Where is the {a} {n1}? It is {rng.choice(PLACE)}.",
            f"Who {rng.choice(VERB)} the {n1}? The {a} {n2} did.",
            f"Is the {n1} {a}? Yes, it is.",
            f"Is the {n1} {a}? No, it is not.",
        ]))

    # short paragraphs: three crisp lines joined by spaces, so 32-byte windows
    # also see sentence-to-sentence structure (capital letter after a period,
    # new sentence on the same topic)
    crisp = [f"The capital of {c} is {v}." for c, v in CAPITALS]
    crisp += PROVERBS
    for item in VERIFY_QA:
        if isinstance(item, tuple):
            crisp.append(item[0] + " " + item[1])
    crisp += [d for d in DIALOGS if "?" in d]
    for _ in range(600):
        picks = rng.sample(crisp, 3)
        add(" ".join(picks))

    rng.shuffle(lines)

    text = "\n".join(lines) + "\n"
    OUT.write_bytes(text.encode("ascii"))
    print(f"wrote {OUT} ({len(text.encode('ascii'))} bytes, {len(lines)} lines)")


if __name__ == "__main__":
    main()
