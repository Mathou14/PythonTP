from itertools import product
import os

class Literals:
    
    def __init__(self,nom,neg):
        self.name = nom
        self.neg = neg

    def __str__(self) -> str:
        if self.neg:
            return f"{self.name}"
        else:
            return f"!{self.name}"
        
    def oppose(self):
        return Literals(self.name,not(self.neg))
    
    def __eq__(self, other):
        if self.name == other.name and self.neg == other.neg:
            return True
        return False
    
    def __hash__(self):
      return hash((self.name, self.neg))

class Rules:

    num_regle = 0

    def __init__(self,s1,s2,b) -> None:
        self.name = Rules.setRef()
        self.premises = s1
        self.conclusion = s2
        self.defeasible = b

    def __str__(self) -> str:
        premises_str = ', '.join(map(str, self.premises))
        #conclusion_str = ', '.join(map(str, self.conclusion))
        conclusion_str = self.conclusion
        if self.defeasible:
            return f"r{self.name} : [{premises_str}] => [{conclusion_str}]"
        return f"r{self.name} : [{premises_str}] -> [{conclusion_str}]"
    
    @classmethod
    def setRef(cls):
        cls.num_regle += 1
        return cls.num_regle
    
    def __eq__(self, other):
        if isinstance(other, Rules):
            return (
                self.premises == other.premises and 
                self.conclusion == other.conclusion and 
                self.defeasible == other.defeasible
            )
        return False
    
    def __hash__(self):
      return hash((self.conclusion, self.defeasible)) * hash(tuple(self.premises))
    
class Argument:
    
    num_arg = 0

    def __init__(self, tr, sa) -> None:
        self.name = Argument.setRef()
        self.topRule = tr
        self.subArg = sa

    def __str__(self) -> str:
        if self.subArg == set():
            if self.topRule.defeasible:
                return f"A{self.name} : => {self.topRule.conclusion}"
            return f"A{self.name} : -> {self.topRule.conclusion}"
        else:
            if self.topRule.defeasible:
                subArg_elements = ", ".join([str(elem.name) for elem in self.subArg])
                return f"A{self.name} : {' '.join([f'A{str(elem.name)}' for elem in self.subArg])} => {self.topRule.conclusion}"

            subArg_elements = ", ".join([str(elem.name) for elem in self.subArg])
            return f"A{self.name} : {' '.join([f'A{str(elem.name)}' for elem in self.subArg])} -> {self.topRule.conclusion}"

    def getName(self):
        return f"A{self.name}"

    def getLiberaleSet(self):
        res = {self.topRule.conclusion}
        for arg in self.subArg:
            res.add(arg.topRule.conclusion)
        return res
    
    def getAllSubArguments(self):
        all_subarguments = []
        stack = [self]
        while stack:
            current_argument = stack.pop()
            all_subarguments.extend(current_argument.subArg)
            stack.extend(current_argument.subArg)
        return all_subarguments

    def getAllDefeasibleRules(self):
        defeasible_rules = set()
        if self.topRule.defeasible:
            defeasible_rules.add(self.topRule)
        for arg in self.subArg:
            if arg.topRule.defeasible:
                defeasible_rules.add(arg.topRule)
            defeasible_rules.update(arg.getAllDefeasibleRules())  # Recursively add defeasible rules of sub-arguments
        return defeasible_rules
    
    def getAllRules(self):
        rules = set()
        rules.add(self.topRule)
        for arg in self.subArg:
            rules.add(arg.topRule)
            rules.update(arg.getAllRules())  # Recursively add defeasible rules of sub-arguments
        return rules
    
    def lastDefeasibleRules(self):
        last_defeasible_rules = set()
        if self.topRule.defeasible:
            last_defeasible_rules.add(self.topRule)
        else:
            for arg in self.subArg:
                last_defeasible_rules.update(arg.lastDefeasibleRules())  # Recursively add last defeasible rules of sub-arguments
        return last_defeasible_rules

    @classmethod
    def setRef(cls):
        cls.num_arg += 1
        return cls.num_arg
    
    @classmethod
    def annulRef(cls):
        cls.num_arg -= 1
    
    def annulArg(self):
        Argument.annulRef()
    
    def __eq__(self,other):
        if isinstance(other, Argument):
            return (
                self.topRule == other.topRule and
                self.subArg == other.subArg
            )
    def __hash__(self):
        return hash((self.topRule)) * hash(tuple(self.subArg))
    
def affEnsemble(s):
    print("-------")
    if s == set():
        print("{}")
        return
    for x in s:
        print(x)

a = Literals("a",True)
b = Literals("b",True)
c = Literals("c",True)
d = Literals("d",True)
e = Literals("e",True)

Nc = Literals("c",False)
Nd = Literals("d",False)

r1 = Rules(set(),a,False)
r2 = Rules({a},Nd,True)
r3 = Rules({b,d},c,False)
r4 = Rules(set(),b,True)
r5 = Rules({Nc},d,False)
r6 = Rules(set(),Nc,True)
r7 = Rules(set(),d,True)
r8 = Rules({c},e,True)

r2L = Literals(2,False)
r9 = Rules({Nc},r2L,True)

set_regles = {r1,r2,r3,r4,r5,r6,r7,r8,r9}

preferences = {}

for rules in set_regles:
    preferences[rules] = 0

preferences[r4] = 1
preferences[r6] = 1

def create_contraposition(l):
    new_rule = set()
    premise = set()
    for rules in l:
        if not(rules.defeasible):
            if rules.premises != set():
                for prem in rules.premises:
                    premise.add(rules.conclusion.oppose())
                    for p in rules.premises:
                        if p!=prem:
                            premise.add(p)
                    new_rule.add(Rules(premise,prem.oppose(),False))
                    premise = set()
    return new_rule

def create_arguments(l):
    args = set()
    deja_traite = set()
    ajoute = set()
    data = set()
    for rule in l:
        if rule.premises == set():
            args.add(Argument(rule,set()))
            deja_traite.add(rule)
            data.add(rule.conclusion)
    tour_supp = False
    if len(args) > 0:
        tour_supp = True
    while(tour_supp):
        tour_supp = False
        for rule in l:
            for argument in args:
                if rule not in deja_traite:
                    if rule.premises.issubset(argument.getLiberaleSet()): #argument.getLiberaleSet().issubset(rule.premises) and 
                        ajoute.add(Argument(rule,argument.subArg|{argument}))
                        deja_traite.add(rule)
        if len(ajoute) > 0:
            for arg in ajoute:
                args.add(arg)
            tour_supp = True
            ajoute = set()
    return args


def create_argument(l):
    args = set()
    deja_traite = set()
    ajoute = set()
    data = set()
    toadd = set()
    for rule in l:
        if rule.premises == set():
            args.add(Argument(rule,set()))
            deja_traite.add(rule)
            data.add(rule.conclusion)
    tour_supp = False
    if len(args) > 0:
        tour_supp = True
    while(tour_supp):
        tour_supp = False
        for rule in l:
            if rule.premises != set():
                if rule.premises.issubset(data):
                    #print(rule)
                    if len(rule.premises) == 1:
                        #print(rule)
                        for lit in rule.premises:
                            #print(lit)
                            la = set()
                            for argument in args:
                                if argument.topRule.conclusion == lit:
                                    la.add(argument)
                            for x in la:
                                a = Argument(rule,{x})
                                if a not in args:
                                    args.add(a)
                                    data.add(rule.conclusion)
                                    tour_supp = True
                                else:
                                    a.annulRef()
                    else:
                        ens = []
                        for lit in rule.premises:
                            la = set()
                            for argument in args:
                                if argument.topRule.conclusion == lit:
                                    la.add(argument)
                            ens.append(la)

                        tab = []
                        tab = product(*ens)
                        
                        for x in tab:
                            a = Argument(rule,set(x))
                            if a not in args:
                                args.add(a)
                                data.add(rule.conclusion)
                                tour_supp = True
                            else:
                                a.annulRef()
    return args

def create_undercut(SetArguments):
    undercutSet = set()
    for arg1 in SetArguments:
        for arg2 in SetArguments:
            for rule in arg2.getAllDefeasibleRules():
                if arg1.topRule.conclusion.name == rule.name and arg1.topRule.conclusion.neg == rule.conclusion.neg and isinstance(arg1.topRule.conclusion.name,int):
                    undercutSet.add((arg1,arg2))
    return undercutSet

def create_rebut(setArguments):
    rebutSet = set()
    for arg1 in setArguments:
        for arg2 in setArguments:
            for rule in arg2.getAllRules():
                if arg1.topRule.conclusion.name == rule.conclusion.name and arg1.topRule.conclusion.neg != rule.conclusion.neg:
                    rebutSet.add((arg1,arg2))
    return rebutSet

def compare_arg(arg1,arg2,principle,link):
    if link == "weakest" and principle=="democratic":
        for rule2 in arg2.getAllDefeasibleRules():
            better = True
            for rule1 in arg1.getAllDefeasibleRules():
                if better:
                    if preferences[rule1] < preferences[rule2]:
                        better = False
            if better:
                return True
        return False
    if link == "weakest" and principle=="elitist":
        better = True
        for rule1 in arg1.getAllDefeasibleRules():
            better = True
            for rule2 in arg2.getAllDefeasibleRules():
                if preferences[rule1] < preferences[rule2]:
                    better = False
            if better:
                return better
        return better
    if link == "last" and principle=="democratic":
        for rule2 in arg2.lastDefeasibleRules():
            better = True
            for rule1 in arg1.lastDefeasibleRules():
                if better:
                    if preferences[rule1] < preferences[rule2]:
                        better = False
            if better:
                return True
        return False
    if link == "last" and principle=="elitist":
        for rule1 in arg1.lastDefeasibleRules():
            better = True
            for rule2 in arg2.lastDefeasibleRules():
                if better:
                    if preferences[rule1] >= preferences[rule2]:
                        better = True
                    else:
                        better = False
            if better:
                return True
        return False
    
#refaire comme rebut
def generate_defeats(setRebuts,principle,link):
    defeatSet = set()
    for arg1,arg2 in setRebuts:
        if compare_arg(arg1,arg2,principle,link):
            defeatSet.add((arg1,arg2))
    return defeatSet

print("Rules set : ")
all_rules = set_regles.union(create_contraposition(set_regles))
for rules in all_rules:
    print(rules)

print()

all_arguments = create_argument(all_rules)
print("nombre d'arguments : " + str(len(all_arguments)))
for arg in all_arguments:
    print(arg)

print()

'''
allSubArgOf = list(all_arguments)[15].getAllSubArguments()
allDefeasibleRules = list(all_arguments)[15].getAllDefeasibleRules()
print(list(all_arguments)[15])
print("ses sous arguments : ")
for x in allSubArgOf:
    print(x)
print("ses regle defeasible : ")
for x in allDefeasibleRules:
    print(x)
print("last defeasible rule :")
for x in list(all_arguments)[15].lastDefeasibleRules():
    print(x)
'''

for x in all_arguments:
    allSubArgOf = x.getAllSubArguments()
    allDefeasibleRules = x.getAllDefeasibleRules()
    print(x)
    print("ses sous arguments : ")
    for y in allSubArgOf:
        print(y)
    print("ses regle defeasible : ")
    for y in allDefeasibleRules:
        print(y)
    print("last defeasible rule :")
    for y in x.lastDefeasibleRules():
        print(y)
    print()

all_undercuts = create_undercut(all_arguments)
print("nombre d'undercuts : " + str(len(all_undercuts)))
for arg1,arg2 in all_undercuts:
    print("" + str(arg1.getName()) + "," +str(arg2.getName()))

print()

all_rebuts = create_rebut(all_arguments)
print("nombre de rebuts : " + str(len(all_rebuts)))
for arg1,arg2 in all_rebuts:
    print("" + str(arg1.getName()) + "," +str(arg2.getName()))

print()

for key in preferences:
    print(key)
    print(preferences[key])
    print("---")

print()

dic = {}
for x in range(1,19):
    dic[x] = 0

all_deafeats = generate_defeats(all_rebuts,"elitist","weakest")
print("nombre de defeats : " + str(len(all_deafeats)))
for arg1,arg2 in all_deafeats:
    dic[arg1.name] += 1
    print("" + str(arg1.getName()) + "," +str(arg2.getName()))

print()

for x in range(1,19):
    print(dic[x])

print()

def generate_ASPARTIX(filename,setArgument,setDefeats):

    with open(filename, "w") as fichier:

    # Vérifier si le fichier est vide
        if not os.path.getsize(filename) == 0:     
        # Vider le fichier
        
            fichier.truncate(0)

    with open(filename, "a") as fichier:
        for args in setArgument:
            fichier.write(f"arg(a{args.name}).\n")
        for arg1,arg2 in setDefeats:
            fichier.write(f"att(a{arg1.name},a{arg1.name}).\n")

def generate_ASPIC(filename,setRules):

    with open(filename, "w") as fichier:

    # Vérifier si le fichier est vide
        if not os.path.getsize(filename) == 0:     
        # Vider le fichier
        
            fichier.truncate(0)

    with open(filename, "a") as fichier:
        for rule in setRules:
            if rule.defeasible:
                fichier.write(f"[r{rule.name}] =>{rule.conclusion} {preferences[rule]}\n")
            else:
                fichier.write(f"[r{rule.name}] ->{rule.conclusion}\n")

generate_ASPARTIX("ASPARTIX.txt",all_arguments,all_deafeats)

generate_ASPIC("ASPIC.txt",all_rules)
