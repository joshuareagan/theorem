### FregeKit ver. 0.001
#
# This is a sketch of a Python library for logic.
# Very likely I will neglect it in favor of a library
# for a language with a stricter type system.

### Classes

class Sentence(object):
    """
    Class for Sentence objects. Each instance represents
    a formal sentence of sentential logic, e.g.

    (A -> A)            :: If A then A
    (~B v C)            :: Either not B or C
    (P <-> ~(A & B))    :: P if and only if not (A and B)
    """

    def sentify(self, s):
        """
        Method for parsing sentence strings into Sentence 
        objects. Returns False if the parse fails.
        """

        next_sent = self._sentify(s)
        if next_sent:
            return next_sent
        else:
            return self._sentify("("+s+")")

    def _sentify(self, s):
        """
        Helper function for sentify; this one
        does most of the work. The structure is 
        recursive, to mirror the recursive definition
        of an SL sentence.
        """

        # Remove whitespace
        s = "".join(s.split())

        # Atomic sentence
        if len(s) == 1:
            if not (s.isupper() and s.isalpha()):
                return False
            else:
                return Atom(s)

        # Negation
        elif s.startswith("~"):
            next_sent = self._sentify(s[1:])

            if not next_sent: return False
            else:
                return Negation(next_sent)

        # Binary connectives
        elif s.startswith("(") and s.endswith(")"):

            s_inner = s[1:-1]
            bracketStack= 0

            # Iterate over all chars in the string
            # looking for the main connective.
            for i, char in enumerate(s_inner):
                if char == "(":
                    bracketStack += 1

                elif char == ")":
                    bracketStack -= 1

                elif bracketStack == 0:
                    if char == ")": return False

                    # conjunctions and disjunctions
                    if char == "&" or char == "v":
                        lhs = self._sentify(s_inner[0:i])
                        rhs = self._sentify(s_inner[i+1:])
                        if not (lhs and rhs): return False
                        elif char == "&": kind = "Conjunction"
                        else: kind = "Disjunction"
                        return Binary(kind, lhs, rhs)

                    # conditionals
                    elif char == "-":

                        if ((len(s_inner) < i + 1) or
                            (s_inner[i+1] != ">")):
                            return False

                        lhs = self._sentify(s_inner[0:i])
                        rhs = self._sentify(s_inner[i+2:])
                        if not (lhs and rhs): return False
                        else:
                            return Binary("Conditional", lhs, rhs)

                    # biconditionals
                    elif char == "<":

                        if ((len(s_inner) < i + 2) or
                            (s_inner[i+1:i+3] != "->")):
                            return False

                        lhs = self._sentify(s_inner[0:i])
                        rhs = self._sentify(s_inner[i+3:])
                        if not (lhs and rhs): return False
                        else:
                            return Binary("Biconditional", lhs, rhs)

        else:
            return False

    def __eq__(self, other):
        """Test for sentence equality"""

        if self.kind != other.kind: return False

        elif self.kind == "Atom" or self.kind == "Negation":
            return self.body == other.body

        else:
            return self.lhs == other.lhs and self.rhs == other.rhs

    def __str__(self):
        """Turn a Sentence into a readable string"""

        connective = {
            "Conjunction": "&",
            "Disjunction": "v",
            "Conditional": "->",
            "Biconditional": "<->"
        }

        if self.kind == "Atom":
            return self.body

        elif self.kind == "Negation":
            return "~" + str(self.body)

        elif (
               self.kind == "Conjunction" or self.kind == "Disjunction" or
               self.kind == "Conditional" or self.kind == "Biconditional"
             ):

            return "({} {} {})".format(
                                         self.lhs,
                                         connective[self.kind],
                                         self.rhs
                                      )
        else:
            return "String conversion Error"

class Atom(Sentence):
    """Class for initializing atomic sentences."""

    def __init__(self, char):
        self.kind = "Atom"
        self.body = char

class Negation(Sentence):
    """Initialize a negation"""
    
    def __init__(self, sentence):
        self.kind = "Negation"
        self.body = sentence

class Binary(Sentence):
    """
    Initialize a sentence whose main connective
    is binary: ->, &, v, <->
    """

    def __init__(self, kind, lhs, rhs):
        self.kind = kind
        self.lhs = lhs
        self.rhs = rhs

class Derivation(object):
    """
    A Derivation instance starts with an assumption of
    an SL sentence followed by a series of rule applications, 
    allowing one to derive new sentences.
    """

    def __init__(self):
        # `rows` is a list of rows that make up the derivation.
        self.rows = []

        # Each assumption introduces a new scope line, which
        # serves as an accounting devise for keeping track of
        # what follows from what.
        self.scopes = []

        # Each scope gets a unique ID, starting with 1.
        self.scope_count = 1

    def append(self, sentence, rule, citations):
        """
        Append a new row to the end of the derivation.
        This function only used for the exchange rules.
        """

        number = self.lastnum() + 1

        if rule == "Assume":
            self.scopes.append(Scope(number, self.scope_count))
            self.scope_count += 1

        new_row = Row(
                       number,
                       len(self.scopes),
                       sentence,
                       rule,
                       citations
                     )

        self.rows.append(new_row)

    def scope_id(self):
        if self.scopes == []:
            return 0
        else:
            scope = self.scopes[-1]
            return scope.id

    def exchange(self, sentence, rule):
        """
        Apply an exchange rule to the last row of 
        the derivation.
        """

        number = self.lastnum()
        self.append(sentence, rule, [number])

    def lastnum(self):
        """Get the last line number used."""

        if self.rows == []: return 0
        else:
            last_row = self.rows[-1]
            return last_row.number

    def add_ion(self, ion):
        scope = self.scopes[-1]
        scope.ions.append(ion)

    def __str__(self):
        """Convert the derivation to a string"""
        
        result = ""

        for row in self.rows:

            scope_lines_string = ""
            for _ in range(row.s_lines):
                scope_lines_string += " |"

            citations_string = ""
            for num in row.citations:
                citations_string += "{}, ".format(num)

            citations_string = citations_string[:-2]

            result += "{}. {} {}    {} {}\n".format(
                row.number,
                scope_lines_string,
                row.sentence,
                row.rule,
                citations_string
            )

        return result

class Row(object):
    """
    Each line has (1) a row number, (2) number of
    open assumptions / scope lines, (3) an SL 
    sentence, (4) a rule, and (5) a list of cited 
    rows.
    """

    def __init__(self, number, s_lines, sentence, rule, citations):
        self.number = number
        self.s_lines = s_lines
        self.sentence = sentence
        self.rule = rule
        self.citations = citations 

class Scope(object):
    """
    Class for scope bookkeeping. The assumption
    value tracks the location of the undischarged
    assumption, and the ions value is a list of ions
    derived so far.
    """
    def __init__(self, number, id):
        self.assumption = number
        self.id = id
        self.ions = []

class Ion(object):
    """
    An ion is either an atomic sentence
    or a negated atomic sentence.
    """
    def __init__(self, number, valence, char):
        self.number = number
        self.valence = valence
        self.char = char

