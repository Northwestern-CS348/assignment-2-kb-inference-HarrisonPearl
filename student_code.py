import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here
        if fact in self.facts:
            ind = self.facts.index(fact)
            if self.facts[ind].asserted and isinstance(fact, Fact):
                self.facts[ind].asserted = False
                self.kb_retract_recursive(self.facts[ind])

    def kb_retract_recursive(self, fact_rule):
        if isinstance(fact_rule, Fact):
            if not fact_rule.supported_by and not fact_rule.asserted:
                for r in fact_rule.supports_rules:
                    for p in r.supported_by:
                        if p[0].statement == fact_rule.statement:
                            r.supported_by.remove(p)
                    self.kb_retract_recursive(r)
                for f in fact_rule.supports_facts:
                    for p in f.supported_by:
                        if p[0].statement == fact_rule.statement:
                            f.supported_by.remove(p)
                    self.kb_retract_recursive(f)
                self.facts.remove(fact_rule)
        if isinstance(fact_rule, Rule):
            if not fact_rule.supported_by and not fact_rule.asserted:
                for r in fact_rule.supports_rules:
                    for p in r.supported_by:
                        if p[1] == fact_rule:
                            r.supported_by.remove(p)
                    self.kb_retract_recursive(r)
                for f in fact_rule.supports_facts:
                    for p in f.supported_by:
                        if p[1] == fact_rule:
                            f.supported_by.remove(p)
                    self.kb_retract_recursive(f)
                self.rules.remove(fact_rule)







        

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        # examine each rule in our KB, and check the first element of its LHS against this new fact
        if isinstance(fact, Fact) and isinstance(rule, Rule):
            # match with constant found
            if fact.statement == rule.lhs[0]:
                if len(rule.lhs) == 1:
                    kb.kb_assert(Fact(rule.rhs), [fact, rule])
                elif len(rule.lhs) > 1:
                    nrule = lc.Rule([rule.lhs[1:], rule.rhs], [(fact, rule)])
                    nrule.asserted = False
                    rule.supports_rules.append(nrule)
                    fact.supports_rules.append(nrule)
                    kb.kb_assert(nrule)

            # match with variable found
            b = match(fact.statement, rule.lhs[0])
            if b:
                if len(rule.lhs) > 1:
                    nlhs = []
                    iterlhs = iter(rule.lhs)
                    next(iterlhs)
                    for S in iterlhs:
                        nlhs.append(instantiate(S, b))
                    nrule = lc.Rule([nlhs, instantiate(rule.rhs, b)], [(fact, rule)])
                    nrule.asserted = False
                    rule.supports_rules.append(nrule)
                    fact.supports_rules.append(nrule)
                    kb.kb_assert(nrule)
                elif len(rule.lhs) == 1:
                    nfact = lc.Fact(instantiate(rule.rhs, b), [(fact, rule)])
                    nfact.asserted = False
                    rule.supports_facts.append(nfact)
                    fact.supports_facts.append(nfact)
                    kb.kb_assert(nfact)

