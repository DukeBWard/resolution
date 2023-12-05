"""
This module defines classes and functions for working with first-order logic clauses and predicates.
It includes the following classes:
- Predicate: represents a predicate with a name, negation, terms, and type.
- Clause: represents a clause with a name and a list of predicates.
And the following functions:
- unify: unifies two predicates using the given substitution.
- unify_variable: unifies a variable with a term using the given substitution.
- unify_predicates: unifies two predicates.
- getFinalForm: gets the final form of a variable name after applying the given substitution.
- getFinalPredicate: gets the final form of a predicate after applying the given substitution.
"""
import sys
from typing import List

FUNCTION_TYPE = "function"
VARIABLE_TYPE = "variable"
PREDICATE_TYPE = "predicate"
CONSTANT_TYPE = "constant"

class Predicate:
    """
    Represents a predicate with a name, negation, terms, and type.
    """
    name = ""
    nameTag = ""
    negated = False
    terms = []
    type = PREDICATE_TYPE

    def __eq__(self, other):
        """
        Check if two predicates are equal.

        Args:
            other (Predicate): The predicate to compare to.

        Returns:
            bool: True if the predicates are equal, False otherwise.
        """
        if self.name == other.name and self.type == other.type and self.negated == other.negated and self.type == other.type:
            return True
        else:
            return False

    def __init__(self, name, negated, terms, type, nameTag):
        """
        Initialize a new Predicate object.

        Args:
            name (str): The name of the predicate.
            negated (bool): Whether the predicate is negated.
            terms (list): The terms of the predicate.
            type (str): The type of the predicate.
            nameTag (str): The name tag of the predicate.
        """
        self.name = name
        self.negated = negated
        self.terms = terms
        self.type = type
        self.nameTag = nameTag

    def __copy__(self):
        """
        Create a copy of the Predicate object.

        Returns:
            Predicate: A copy of the Predicate object.
        """
        return Predicate(self.name, self.negated, self.terms.copy(), self.type)

    def __hash__(self):
        """
        Get the hash value of the Predicate object.

        Returns:
            int: The hash value of the Predicate object.
        """
        return self.name.__hash__()

    def __str__(self):
        """
        Get the string representation of the Predicate object.

        Returns:
            str: The string representation of the Predicate object.
        """
        if self.type == VARIABLE_TYPE or self.type == CONSTANT_TYPE:
            return self.name

        return "!" + self.name if self.negated else "" + self.name  # + "(" + termString + ")"


class Clause:
    """
    Represents a clause with a name and a list of predicates.
    """
    predicates: List[Predicate] = list()
    name = ""

    def __init__(self, name, predicates):
        """
        Initialize a new Clause object.

        Args:
            name (str): The name of the clause.
            predicates (list): The predicates of the clause.
        """
        self.predicates = predicates
        self.name = name

    def __str__(self):
        """
        Get the string representation of the Clause object.

        Returns:
            str: The string representation of the Clause object.
        """
        string = ""
        for predicate in self.predicates:
            string += predicate.__str__() + " "
        return string

    def __hash__(self):
        """
        Get the hash value of the Clause object.

        Returns:
            int: The hash value of the Clause object.
        """
        return self.name.__hash__()

    def __eq__(self, other):
        """
        Check if two Clause objects are equal.

        Args:
            other (Clause): The Clause object to compare to.

        Returns:
            bool: True if the Clause objects are equal, False otherwise.
        """
        if len(self.predicates) == 0 and len(other.predicates) == 0 and self.name == other.name:
            return True
     
        if self.name == other.name:
            if len(self.predicates) == len(other.predicates):
                for i in range(len(self.predicates) - 1):
                    if self.predicates[i].__eq__(other.predicates[i]):
                        continue
                    else:
                        return False
            else:
                return False
        else:
            return False

        return True


def unify(t1: Predicate, t2: Predicate, oldTheta: dict):
    """
    Unifies two predicates using the given substitution.

    Args:
        term1 (Predicate): The first predicate to unify.
        term2 (Predicate): The second predicate to unify.
        oldTheta (dict): The substitution to use.

    Returns:
        dict: The resulting substitution.
    """
    theta = oldTheta.copy()
    if t1 == t2:
        return theta
    elif t1.type == VARIABLE_TYPE:
        uni_var_res = unify_variable(t1, t2, theta)
        if uni_var_res is not None:
            return theta | uni_var_res

        else:
            return None
    elif t2.type == VARIABLE_TYPE:

        uni_var_res = unify_variable(t2, t1, theta)
        if uni_var_res is not None:
            return theta | uni_var_res
        else:
            return None
    elif t2.type == FUNCTION_TYPE and t1.type == FUNCTION_TYPE:
        # verify both term names match
        if t1.name[:t1.name.index("(")] != t2.name[:t2.name.index("(")]:
            return None

        # unify each argument for these function with every other argument from function 2 (checks if terms can unify)
        for termOuter in t1.terms:
            for termInner in t2.terms:
                uni_res = unify(termInner, termOuter, theta)
                if uni_res is None:
                    return None
                theta = theta | uni_res

        return theta
    else:
        return None

def unify_variable(variable, term2, theta):
    """
    Unifies a variable with a term using the given substitution.

    Args:
        variable (Predicate): The variable to unify.
        term2 (Predicate): The term to unify with.
        theta (dict): The substitution to use.

    Returns:
        dict: The resulting substitution.
    """
    unifications = theta
    # if this variable has already been mapped to some other variable/constant, then unify those instead
    if variable.name in unifications.keys():
        linked_var_name = getFinalForm(variable.name, unifications)
        new_var_term = variable.__copy__()
        new_var_term.name = linked_var_name

        unifications = unifications | unify(new_var_term, term2, unifications)
    elif term2.name in unifications.keys():
        linkedTermName = getFinalForm(term2.name, unifications)
        newTerm = term2.__copy__()
        newTerm.name = linkedTermName
        unifications = unifications | unify(variable, newTerm, unifications)

    else:
        unifications[variable.name] = term2.name

    return unifications

def unify_predicates(p1: Predicate, p2: Predicate) -> dict:
    """
    Unifies two predicates.

    Args:
        p1 (Predicate): The first predicate to unify.
        p2 (Predicate): The second predicate to unify.

    Returns:
        dict: The resulting substitution.
    """
    unification_theta = {}
    for i in range(len(p1.terms)):
        tempTheta = unify(p1.terms[i], p2.terms[i], unification_theta)

        if tempTheta is None:
            return None
        else:
            unification_theta = tempTheta | unification_theta

    return unification_theta

def getFinalForm(variableName, theta):
    """
    Gets the final form of a variable name after applying the given substitution.

    Args:
        variableName (str): The variable name to get the final form of.
        theta (dict): The substitution to use.

    Returns:
        str: The final form of the variable name.
    """
    translated = variableName
    # if there is a translation at this level
    if translated in theta.keys():
        # translate it and also check to see if it can be further translated
        translated = theta[translated]

        translated = getFinalForm(translated, theta)

    return translated


def getFinalPredicate(predicate, theta):
    newTerms = []

    for term in predicate.terms:
        if term.type == CONSTANT_TYPE:
            newTerms.append(term)
        elif term.type == VARIABLE_TYPE:
            # get final form will get the final string evaluation of the variable
            final_form = getFinalForm(term.name, theta)
  
            new_var = None
            if final_form in constants:
                new_var = Predicate(final_form, False, [], CONSTANT_TYPE, final_form)
            elif final_form in variables:
                new_var = Predicate(final_form, False, [], VARIABLE_TYPE, final_form)
            else:
                # must be a function as it cannot be a predicate or a clause
                if ("(" in final_form):
                    # returns a function based on the term string
                    new_var = termParser(final_form, variables, constants)
                else:
                    print("error")
                    exit()

            newTerms.append(new_var)
        elif term.type == FUNCTION_TYPE:
           
            finalFunction = getFinalPredicate(term, theta)
            newTerms.append(finalFunction)

    newName = predicate.nameTag + "("
    for term in newTerms:
        newName += " " + term.name

    newName += " )"

    return Predicate(newName, predicate.negated, newTerms, predicate.type, predicate.nameTag)


def resolve(clause1: Clause, clause2: Clause):
    global_unification = {}
    out_clause = []

    # take two clauses, attempt to combine predicates in every which way
    resolved_predicates = set()

    for c1_pred in clause1.predicates:
        for c2_pred in clause2.predicates:


            if c2_pred.nameTag == c1_pred.nameTag and c1_pred.negated != c2_pred.negated:
                if c1_pred.terms == [] and c2_pred.terms == []:
        
                    resolved_predicates.add(c1_pred)
                    resolved_predicates.add(c2_pred)
                    output_pred = []
                    new_name = ""
                    for c1_pred_combine in clause1.predicates:
               
                        if c1_pred_combine is c1_pred:
                            continue
                        else:
                            output_pred.append(c1_pred_combine)
                            new_name += "!" if c1_pred_combine.negated else "" + c1_pred_combine.name + " "

                    for c2_pres_combine in clause2.predicates:
                        if c2_pres_combine is c2_pred:
                            continue
                        else:
                            output_pred.append(c2_pres_combine)
                            new_name += "!" if c2_pres_combine.negated else "" + c2_pres_combine.name + " "

                    out_clause.append(Clause(new_name, output_pred))
                    continue

               
                # once it might be possible to unify the two predicates, begin to march through their arguments and try to unify the two
                pred_uni = unify_predicates(c1_pred, c2_pred)
                if pred_uni is None:
                    continue
                else:
                    global_unification = global_unification | pred_uni.copy()
                    # create an output clause that excludes these two since these two were able to unify
                    resolved_predicates.add(c1_pred)
                    resolved_predicates.add(c2_pred)
                    output_pred = []
                    new_name = ""
                    for c1_pred_combine in clause1.predicates:
                        if c1_pred_combine.name == c1_pred.name:
                            continue
                        else:
                            output_pred.append(
                                getFinalPredicate(c1_pred_combine, global_unification))
                            new_name += "!" if c1_pred_combine.negated else "" + c1_pred_combine.name + " "
                    for c2_pres_combine in clause2.predicates:
                        if c2_pres_combine.name == c2_pred.name:
                            continue
                        else:
                            output_pred.append(
                                getFinalPredicate(c2_pres_combine, global_unification))
                            new_name += "!" if c2_pres_combine.negated else "" + c2_pres_combine.name + " "

                    out_clause.append(Clause(new_name, output_pred))
                    # then add parent clauses


    out_clause.append(clause1)
    out_clause.append(clause2)

    return out_clause


def Union(list1, list2):
    outputList = list(set(list1) | set(list2))
    return outputList


def resolver(clauses):
    current_clauses = set(clauses.copy())
    new_clause = set()

    while (True):
        clause_loop = list(current_clauses)
        for c1_index in range(len(clause_loop)):
            for c2_index in range(c1_index + 1, len(clause_loop)):
                c1 = clause_loop[c1_index]
                c2 = clause_loop[c2_index]
                resolvents = resolve(c1, c2)
                # make sure this works
                if Clause("", []) in resolvents:
                    print("no")
                    exit()

                # add these newly generated clauses to the newClauses
                new_clause = new_clause | set(resolvents)
    

        # if no new clauses are generated, return "NO" otherwise, add these new clauses to the set of current clauses
        if new_clause.issubset(set(current_clauses)):
            print("yes")
            exit()
        else:
            current_clauses = current_clauses | new_clause

def termParser(term_str, variables: set, constants: set):
    out_term = None
    # if is function
    term_str = term_str.strip()

    if "(" in term_str:
        out_term = Predicate(term_str, False, [], FUNCTION_TYPE, nameTag=term_str[:term_str.index("(")])
        # get index of both parenthesis
        first_paren = term_str.index("(")
        second_paren = len(term_str) - 1

        func_args = term_str[first_paren + 1: second_paren].split(",")

        for arg in func_args:
            out_term.terms.append(termParser(arg, variables, constants))

        return out_term
    elif term_str in variables:
        out_term = Predicate(term_str, False, [], VARIABLE_TYPE, term_str)
        return out_term
    elif term_str in constants:
        out_term = Predicate(term_str, False, [], CONSTANT_TYPE, term_str)
        return out_term
    else:
        raise Exception("error bad parse")
   

def parseInput(inputFile):
    File = open(inputFile, 'r')

    predicates = set()
    variables = set()
    constants = set()
    functions = set()
    clauses = list()

    lines = []
    for line in File:
        lines.append(line.strip())

    split_line = lines[0].split()

    for value in split_line[1:]:
        predicates.add(value.strip())

    split_line = lines[1].split()

    for value in split_line[1:]:
        variables.add(value.strip())

    split_line = lines[2].split()

    for value in split_line[1:]:
        constants.add(value.strip())

    split_line = lines[3].split()

    for value in split_line[1:]:
        functions.add(value.strip())

    for i in range(5, len(lines)):
        clauses.append(lines[i].rstrip())

    # create clause objects:

    clause_obj = []
    for clause in clauses:
        sub_clause = clause.split()
        # find predicates in clause
        pred_obj = []
        for predicate in sub_clause:
            if "(" not in predicate:
                predicate = predicate + "()"
                if predicate[0] == "!":
                    pred_obj.append(Predicate(predicate[1:predicate.index("(")], True, [], PREDICATE_TYPE,
                                                       predicate[1:predicate.index("(")]))
                else:
                    pred_obj.append(Predicate(predicate[0:predicate.index("(")], False, [], PREDICATE_TYPE,
                                                       predicate[0:predicate.index("(")]))
                continue

            negated = False
            terms = []
            terms_of_pred = predicate[predicate.index("(") + 1: len(predicate) - 1]
            parsedTerms = terms_of_pred.split(',')

            for term in parsedTerms:
                terms.append(termParser(term, variables, constants))

            if predicate[0] == "!":
                negated = True
                
                pred_obj.append(Predicate(predicate[1:predicate.index("(")], negated, terms, PREDICATE_TYPE,
                                                   predicate[1:predicate.index("(")]))
            else:
                pred_obj.append(Predicate(predicate[0:predicate.index("(")], negated, terms, PREDICATE_TYPE,
                                                   predicate[0:predicate.index("(")]))
        clause_obj.append(Clause(clause, pred_obj))

    File.close()

    return predicates, variables, constants, functions, clause_obj

if __name__ == '__main__':
    predicates, variables, constants, functions, clauses = parseInput(sys.argv[1])

    resolver(clauses)
