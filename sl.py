### sl.py
#
# This program takes any SL sentence S and displays either:
#
#   (1) a valuation that makes S false, or
#
#   (2) a derivation of S, which demonstrates that it's a
#       logical truth, i.e., true on all valuations.
#
# SL (= sentential logic) is formally decidable, so this 
# program should give an appropriate answer for any valid 
# input value. (Assuming no bugs!)

from FregeKit import sentify, Derivation, Ion, Atom, Negation, Binary

# The input sentence.
sl_sentence = "(A -> B) -> (~B -> ~A)"

# Create a new derivation.
derivation = Derivation()

def main():

    sent_obj = sentify(sl_sentence)
    if not sent_obj:
        print("Not a sentence!")
    else:
        print(sent_obj)
        completed = derive(sent_obj)
        if completed: print(derivation)

def derive(sentence):
    """
    Attempt to derive a given sentence. If this can't be
    done, return a counterexample.
    """
    # Assume the opposite
    next_sent = Negation(sentence)
    assume(next_sent)

    # Convert sentence to disjunctive normal form (DNF)
    dnf_sent = dnf(next_sent)

    # Check for a counterexample.
    ce_found, ce = find_ce(dnf_sent)

    if ce_found:
        print("Counterexample found:")
        for char in ce:
            print("    {}: {}".format(char, ce[char]))
        return False

    else:
        # No CE exists, so complete the derivation.
        print("Success!")
        reductio(dnf_sent, None)
        return True

def dnf(sentence):
    """
    Takes an SL sentence and returns an equivalent one 
    that's in disjunctive normal form (DNF).
    """
    next_sent = remove_arrows(sentence)
    next_sent = negation_push(next_sent)
    next_sent = de_conjunctify(next_sent)
    return next_sent

def find_ce(dnf_sent):
    """
    Takes a DNF sentence and checks for a valuation that 
    makes it true. If found, this valuation is returned.
    """

    # Break up sentence by disjunct
    sent = str(dnf_sent)
    disjuncts = sent.split("v")

    # Check each disjunct for truth-making valuation.
    for disjunct in disjuncts:
        pos = set()
        neg = set()

        # Positive ions go in pos, negative ions in neg.
        d_iter = iter(disjunct)        
        for char in d_iter:
            if char == "~":
                neg.add(next(d_iter))
            elif char.isalpha():
                pos.add(char)
     
        # If an atom is affirmed and denied, e.g. P & ~P,
        # there's no truth-making valuation.
        if pos.intersection(neg): continue

        # Counterexample found, return it
        else:
            counterexample = {}
            for char in sent:
                if char.isalpha() and char.isupper():
                    counterexample[char] = False
            for char in pos:
                counterexample[char] = True

            return True, counterexample

    return False, None

### Exchange functions
#
# These functions are for converting a sentence to 
# disjunctive normal form.

def remove_arrows(sentence):
    """
    Replaces any sentence with a logically equivalent
    one lacking arrows, -> and <->.
    """
    return exchange_rule_loop(sentence, _remove_arrows)

def exchange_rule_loop(sentence, func):
    """
    Applies exchange rules repeatedly until they no 
    longer apply.
    """
    next_sent, rule = func(sentence)

    while next_sent != sentence:
        derivation.exchange(next_sent, rule)
        sentence = next_sent
        next_sent, rule = func(sentence)

    return next_sent

def _remove_arrows(sentence):
    """
    Check for arrows, -> and <->, and remove the first one
    found. Return a pair: (1) the new sentence, (2) the 
    exchange rule used to remove the arrow.
    """

    kind = sentence.kind

    # Atomic sentence
    if kind == "Atom":
        return sentence, None

    # Negation
    elif kind == "Negation":
        next_body, rule = _remove_arrows(sentence.body)
        return Negation(next_body), rule

    # Binary connective sentence
    else:
        lhs, rhs = sentence.lhs, sentence.rhs

        # Check the subsentences for arrows.
        next_sent, rule = subsent_check(sentence, _remove_arrows)
        if rule: return next_sent, rule
        
        # Check the main connective for arrow.
        if kind == "Conditional":

            # Exchange (P -> Q) for (~P v Q)
            next_sent = Binary("Disjunction", Negation(lhs), rhs)
            return next_sent, "-> exch."

        elif kind == "Biconditional":

            # Exchange (P <-> Q) for ((P & Q) v (~P & ~Q))
            next_lhs = Binary("Conjunction", lhs, rhs)
            next_rhs = Binary("Conjunction", Negation(lhs), Negation(rhs))
            next_sent = Binary("Disjunction", next_lhs, next_rhs) 
            return next_sent, "<->/v exch."

        else:
            return sentence, None

def subsent_check(sentence, func):
    """
    Helper function for DNF functions. Takes a binary 
    sentence and checks whether an exchange function,
    func(), applies to either of its subsentences.
    """
    kind, lhs, rhs = sentence.kind, sentence.lhs, sentence.rhs

    next_lhs, rule = func(lhs)
    if rule: return Binary(kind, next_lhs, rhs), rule

    next_rhs, rule = func(rhs)
    if rule: return Binary(kind, lhs, next_rhs), rule

    return sentence, None

def negation_push(sentence):
    """
    Takes an arrow-less sentence and returns an 
    equivalent one whose negations only govern
    atoms.
    """
    return exchange_rule_loop(sentence, _negation_push)

def _negation_push(sentence):
    """
    Move negations in until they only govern atoms. This
    function only makes one change at a time. Returns a 
    pair of (1) new sentence & (2) rule applied.
    """
    kind = sentence.kind

    if kind == "Atom":
        return sentence, None

    elif kind == "Negation":
        body = sentence.body
        inner_kind = body.kind

        if inner_kind == "Atom":
            return sentence, None

        elif inner_kind == "Negation":
            inner_body = body.body
            next_inner_body, rule = _negation_push(inner_body)

            if next_inner_body != inner_body:
                return Negation(Negation(next_inner_body)), rule

            else:
                # Exchange ~~P for P.
                return inner_body, "~~ elim."

        # Negation of binary connective: ~(P & Q) or ~(P v Q)
        else:
            lhs, rhs = body.lhs, body.rhs

            # Check the negations in the subsentences.
            next_sent, rule = subsent_check(body, _negation_push)
            if rule: return Negation(next_sent), rule

            # Apply De Morgan's rule
            elif inner_kind == "Conjunction":
                # Exchange ~(P & Q) for (~P v ~Q)
                return Binary("Disjunction", 
                                 Negation(lhs),
                                 Negation(rhs)
                             ), "De Morgan's"
            else:
                # Exchange ~(P v Q) for (~P & ~Q)
                return Binary("Conjunction", 
                                 Negation(lhs),
                                 Negation(rhs)
                             ), "De Morgan's"

    # Binary connective case
    else:
        return subsent_check(sentence, _negation_push)

def de_conjunctify(sentence):
    """
    Takes an arrow-less sentence with negations pushed in,
    and returns an equivalent sentence in which no 
    conjunction governs a disjunction.
    """
    return exchange_rule_loop(sentence, _de_conjunctify)

def _de_conjunctify(sentence):
    """
    If a conjunction governs a disjunction, exchange for
    an equivalent sentence in which this isn't so.
    """
    kind = sentence.kind

    if kind == "Atom" or kind == "Negation":
        return sentence, None

    # Binary connective case
    else:
        lhs, rhs = sentence.lhs, sentence.rhs

        # Check the subsentences.
        next_sent, rule = subsent_check(sentence, _de_conjunctify)
        if rule: return next_sent, rule

        elif kind == "Disjunction":
            return sentence, None

        # Conjunction case
        elif lhs.kind == "Disjunction":
            # Exchange ((P v Q) & R) for ((P & R) v (Q & R))
            return Binary("Disjunction",
                             Binary("Conjunction", lhs.lhs, rhs),
                             Binary("Conjunction", lhs.rhs, rhs)
                         ), "&/v exch."

        elif rhs.kind == "Disjunction":
            # Exchange (P & (Q v R)) for ((P & Q) v (P & R))
            return Binary("Disjunction",
                             Binary("Conjunction", lhs, rhs.lhs),
                             Binary("Conjunction", lhs, rhs.rhs)
                         ), "&/v exch."

        else:
            return sentence, None

### Reductio ad absurdum
#
# This is the main function for completing the derivation
# after it's in DNF.

def reductio(sentence, goal):
    """
    Given a DNF sentence w/o a counterexample, work to a 
    contradiction and derive the opposite, completing the 
    derivation.
    """
    kind = sentence.kind

    if kind == "Atom" or kind == "Negation":
        return contra_check(sentence, goal)

    if kind == "Disjunction":
        next_sent = v_elim(sentence.lhs, sentence.rhs)
        next_sent = arrow_intro(next_sent)
        return reductio(next_sent, None)

    if kind == "Conjunction":
        return and_elim(sentence.lhs, sentence.rhs, goal)

    if kind == "Conditional":
        if len(derivation.scopes) == 0:
            return neg_elim(sentence.lhs)
        else:
            return sentence

def contra_check(sentence, goal):
    """
    Checks whether contradictory ions have been derived,
    e.g. P and ~P.
    """
    number = derivation.lastnum()
    valence = sentence.kind == "Atom"
    char = sentence.body if valence else sentence.body.body

    derivation.add_ion(Ion(number, valence, char))

    for scope in derivation.scopes:
        for ion in scope.ions:
            if ion.char == char and ion.valence != valence:
                # Contradiction found

                next_sent = and_intro(char, ion.number, number)
                if goal and next_sent != goal:
                    # From a contradiction, anything follows.
                    derivation.exchange(goal, "Any Contra.")
                    next_sent = goal
                    goal = None

                next_sent = arrow_intro(next_sent)
                return reductio(next_sent, goal)

    return sentence

### Rules
#
# This section contains functions for applying formal
# rules to the derivation until it's complete.

def and_elim(lhs, rhs, goal):
    """(P & Q) => P, Q"""
    number = derivation.lastnum()
    derivation.append(lhs, "& elim", [number])

    scope_id = derivation.scope_id()
    next_sent = reductio(lhs, goal)

    # Check whether an assumption was discharged
    # in previous reductio() call
    if scope_id != derivation.scope_id():
        return next_sent
    else:
        derivation.append(rhs, "& elim", [number])
        return reductio(rhs, goal)

def and_intro(char, cite_1, cite_2):
    """P, ~P => (P & ~P)"""
    sent = Binary("Conjunction", Atom(char), Negation(Atom(char)))
    derivation.append(sent, "& intro.", [cite_1, cite_2])
    return sent

def arrow_intro(rhs):
    """
    Discharge an assumption.

    | P   Assume
    | ...
    | Q
    (P -> Q)
    """
    scope = derivation.scopes.pop()
    lhs_line = scope.assumption
    rhs_line = derivation.lastnum()
    lhs = derivation.rows[lhs_line-1].sentence

    next_sent = Binary("Conditional", lhs, rhs)
    derivation.append(next_sent, "-> intro.", [lhs_line, rhs_line])
    return next_sent

def assume(sentence):
    """
    Make an assumption.

    | P   Assume
    | ...
    """
    derivation.append(sentence, "Assume", [])
    return sentence

def v_elim(lhs, rhs):
    """(P v Q), (P -> R), (Q -> R) => R"""
    line_1 = derivation.lastnum()
    first_arrow = reductio(assume(lhs), None)
    line_2 = derivation.lastnum()

    goal = first_arrow.rhs
    reductio(assume(rhs), goal)
    line_3 = derivation.lastnum()

    derivation.append(goal, "v elim.", [line_1, line_2, line_3])
    return goal

def neg_elim(sentence):
    """(~P -> (Q & ~Q)) => P"""
    derivation.exchange(sentence.body, "~ elim.")
    return sentence.body

if __name__ == "__main__":
    main()
