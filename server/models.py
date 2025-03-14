## DO NOT MODIFY; COPY FROM BABEL

from dataclasses import dataclass, field
from typing import Dict, Any, List, Optional, Tuple, Type, Literal, Iterator, Set
import json
import os
import re

import tqdm
import numpy as np
import torch


SimpAllHint = Literal[
    "notInSimpAll",
    "unmodified",
    "simpErase",
    "simpPreOnly",
    "simpPostOnly",
    "backwardOnly",
    "simpPreAndBackward",
    "simpPostAndBackward",
]


@dataclass
class BaseInfo():
    """Base class for State, Premise"""

    name: str
    """A (unique) identifier of the object"""

    module: str
    """The Lean module in_name which this object resides"""

    line: int
    """The line in `module` on which this object resides"""

    column: int
    """The column on `line` on which this object resides"""

    idx_in_module: int
    """Index of this object in `module` for internal debugging use
    (this field is incorrect for Premise)"""

    @classmethod
    def from_dict(cls, module: str, idx_in_module: int, info: Dict[str, Any]):
        """Load info from a dictionary extracted by ntp-toolkit."""
        raise NotImplementedError

    def to_string(self) -> str:
        """Turn the information to a string as part of a prompt to language models."""
        raise NotImplementedError


@dataclass
class State(BaseInfo):
    """State represents an intermediate state in a tactical proof immediately before a tactic"""

    state: str
    """State before the tactic"""

    source_up_to_tactic: Optional[str]
    """Raw source in module up to next tactic (None for conserving space)"""

    # decl: str
    # """The raw declaration string in which this state is found"""

    decl_name: str
    """The qualified name of the declaration in which the state is found"""

    def to_string(self):
        return self.state


@dataclass
class StateWithTactic(State):
    """A state with a known ground truth tactic (for training)"""

    next_tactic_hammer_recommendation: List[str]
    """Constants for hammer recommendation in the next tactic.
    For consistency, use `RetrievalDataset.relevant_premises` and `RetrievalDataset.pairs` instead.
    """

    next_tactic_simp_all_hints: Dict[str, SimpAllHint]
    """Hints assigned to each premise in `next_tactic_hammer_recommendation`"""

    hammer_recommendation: List[str]
    """Constants for hammer recommendation in tactics for this state (e.g. until end of goal).
    For consistency, use `RetrievalDataset.relevant_premises` and `RetrievalDataset.pairs` instead (which filters to only premises in corpus).
    """

    simp_all_hints: Dict[str, SimpAllHint]
    """Hints assigned to each premise in `hammer_recommendation`"""

    # next_tactic_is_simp_or_rw_variant: bool
    # """Whether the next tactic is simp* or rw*"""

    next_tactic: str
    """The raw string of the next tactic"""

    @classmethod
    def from_dict(cls, module: str, idx_in_module: int, info: Dict[str, Any]):
        def parse_hammer_recommendation(recommendation: List[str]):
            names = []
            hints = {}
            for r in recommendation:
                assert r.startswith("(")
                name, simp_all_hint = r[1:-1].split(", ")
                names.append(name)
                hints[name] = simp_all_hint
            return names, hints
        assert "hammerRecommendationToEndOfGoal" not in info  # TODO: update logic if toendofgoal is added back in
        hammer_recommendation, simp_all_hints = parse_hammer_recommendation(
            info.get("hammerRecommendationToEndOfGoal", info["declHammerRecommendation"])
        )
        next_tactic_hammer_recommendation, next_tactic_simp_all_hints = parse_hammer_recommendation(
            info["nextTacticHammerRecommendation"]
        )
        return cls(
            name=f"{module}#{idx_in_module}",
            module=module,
            idx_in_module=idx_in_module,
            line=info["srcUpToTactic"].count("\n"),
            column=len(info["srcUpToTactic"]) - info["srcUpToTactic"].rfind("\n"),
            state=info["state"],
            next_tactic_hammer_recommendation=next_tactic_hammer_recommendation,
            next_tactic_simp_all_hints=next_tactic_simp_all_hints,
            hammer_recommendation=hammer_recommendation,
            simp_all_hints=simp_all_hints,
            # next_tactic_is_simp_or_rw_variant=info["nextTacticIsSimpOrRwVariant"],
            next_tactic=info["nextTactic"],
            source_up_to_tactic=None,
            # decl=info["decl"],
            decl_name=info["declName"],
        )


@dataclass
class Premise(BaseInfo):
    """A Premise is a Lean constant to be used by tactics"""

    kind: str
    """Declaration type (def / theorem / ...)"""

    args: List[str]
    """List of pretty-printed arguments"""

    type: str
    """Pretty-printed resulting type"""

    doc: Optional[str]
    """Docstring, if exists"""

    is_prop: bool
    """The type of this constant is Prop-valued"""

    can_benchmark: bool
    """Premise can be used for benchmarking, for determining eval/test set"""

    @classmethod
    def from_dict(cls, module: str, idx_in_module: int, info: Dict[str, Any]):
        return cls(
            module=module,
            idx_in_module=idx_in_module,
            kind=info["kind"],
            name=info["name"],
            args=info["args"],
            type=info["type"],
            doc=info["doc"],
            line=info["line"],
            column=info["column"],
            is_prop=info["isProp"],
            can_benchmark=info["isHumanTheorem"],
        )

    def to_string(self):
        args = " ".join(self.args)
        prettified = f"{self.kind} {self.name} {args} : {self.type}"
        if self.doc is not None:
            prettified = f"/-- {self.doc.strip()} -/\n{prettified}"
        return prettified


class SimplePremise(Premise):
    """A premise that only has name, pretty-printed string, and module information"""
    def __init__(self, name: str, decl: str, module: str):
        self.decl: str = decl
        # HACK: here the irrelevant fields are given junk values
        Premise.__init__(self, name, module, 0, 0, 0, "", [], "", None, True, True)

    def to_string(self):
        return self.decl


def read_ntp_toolkit(
    data_dir: str,
) -> Iterator[Tuple[str, int, Dict[str, Any]]]:
    """Internal method that reads .jsonl files from ntp-toolkit"""
    for json_file in tqdm.tqdm(sorted(os.listdir(data_dir))):
        if json_file.endswith(".jsonl"):
            module = json_file.removesuffix(".jsonl")
            with open(os.path.join(data_dir, json_file)) as f:
                for i, line in enumerate(f):
                    # # Temporary fix for a version of ntp-toolkit, can remove
                    # line = re.sub(r"^\S+ data:\s*", "", line)
                    info_dict = json.loads(line)
                    yield (module, i, info_dict)

def read_ntp_toolkit_modules(
    data_dir: str
) -> Iterator[str]:
    """Internal method that reads module names from ntp-toolkit"""
    for json_file in tqdm.tqdm(sorted(os.listdir(data_dir))):
        if json_file.endswith(".jsonl"):
            module = json_file.removesuffix(".jsonl")
            yield module

class PremiseSet:
    """Represents a set of premises.

    This is an efficient implementation, similar to PremiseSet from LeanDojo ReProver,
    storing a set of premises from a set of modules, plus small number of individual premises.
    """
    def __init__(self, corpus: "Corpus", modules: Set[str]):
        self.corpus = corpus
        # Invariant: self._added is disjoint with (premises in self._modules that are in corpus)
        #   self._added, self._added_name2idx and self._modules, self._modules_name2idx are in correspondence
        # The set represented by self = self._added U (premises in self._modules that are in corpus)
        self._modules = list(modules)
        self._modules_name2idx: Dict[str, int] = {module: i for i, module in enumerate(self._modules)}
        self._added: List[str] = []
        self._added_name2idx: Dict[str, int] = {}

    def __contains__(self, premise: Premise) -> bool:
        if premise.name in self._added_name2idx:
            return True
        if premise.module in self._modules_name2idx and premise.name in self.corpus.name2premise:
            return True
        return False

    def __len__(self) -> int:
        size = len(self._added)
        for module in self._modules:
            if module in self.corpus.module_to_premises:
                size += len(self.corpus.module_to_premises[module])
        return size

    def __iter__(self) -> Iterator[Premise]:
        for name in self._added:
            yield self.corpus.name2premise[name]
        for module in self._modules:
            if module in self.corpus.module_to_premises:
                for name in self.corpus.module_to_premises[module]:
                    yield self.corpus.name2premise[name]

    def __getitem__(self, i: int) -> Premise:
        i = i % len(self)
        if i < len(self._added):
            return self.corpus.name2premise[self._added[i]]
        i -= len(self._added)
        for module in self._modules:
            if module in self.corpus.module_to_premises:
                module_premises = self.corpus.module_to_premises[module]
                if i < len(module_premises):
                    return self.corpus.name2premise[module_premises[i]]
                i -= len(module_premises)
        assert False  # code should not reach here

    def add(self, premise: Premise):
        if premise not in self:
            self._added_name2idx[premise.name] = len(self._added)
            self._added.append(premise.name)

    def remove(self, premise: Premise):
        if premise.name in self._added_name2idx:
            i = self._added_name2idx.pop(premise.name)
            last_name = self._added.pop()
            if i != len(self._added):
                self._added[i] = last_name
                self._added_name2idx[last_name] = i
        elif premise.module in self._modules_name2idx and premise.name in self.corpus.name2premise:
            # We remove this module from self._modules and
            # add every premise in it except `premise` to self._added
            i = self._modules_name2idx.pop(premise.module)
            last_module = self._modules.pop()
            if i != len(self._modules):
                self._modules[i] = last_module
                self._modules_name2idx[last_module] = i
            for other_premise_name in self.corpus.module_to_premises[premise.module]:
                assert other_premise_name not in self._added_name2idx
                if other_premise_name != premise.name:
                    self._added_name2idx[other_premise_name] = len(self._added)
                    self._added.append(other_premise_name)

    def sample(self, size: int, generator: Optional[torch.Generator] = None) -> List[Premise]:
        if len(self) == 0:  # extreme exception
            return [Premise("", "Init.Prelude", 0, 0, 0, "", [], "", None, False, False) for _ in range(size)]
        if generator is not None:
            indices = torch.randint(len(self), (size,), generator=generator).tolist()
        else:
            indices = np.random.choice(len(self), size, replace=True).tolist()
        return [self[i] for i in indices]


class Corpus:
    """A data store of defined `Premise`s"""

    # Blacklists for filtering premises from from_ntp_toolkit
    # This filter should be consistent with any Lean code that e.g. sends new user-defined premises to the server

    # Modules with MODULE_BLACKLIST in any component of its name are filtered out
    MODULE_BLACKLIST = [
        "Aesop", "Auto", "Cli", "CodeAction", "DocGen4", "Duper", "ImportGraph", "Lake", "Lean", "LeanSearchClient", "Linter", "Mathport",
        "MD4Lean", "Plausible", "ProofWidgets", "Qq", "QuerySMT", "Tactic", "TacticExtra", "Test", "Testing", "UnicodeBasic", "Util",
    ]

    # Premises with NAME_BLACKLIST in any component of its name are filtered out
    NAME_BLACKLIST = ["Lean", "Lake", "Qq"]

    # Premises with resulting type starting with "Lean" are filtered out (Lean.ParserDescr, etc.)
    TYPE_PREFIX_BLACKLIST = ["Lean."]

    IS_PROP_FILTER = False

    # On the one hand many math proofs will use lemmas in these.
    # On the other hand, in this case we should use the tactics directly instead of Hammer at test time.
    # MODULE_WHITELIST = ["Mathlib.Tactic"]
    # NAME_WHITELIST = ["Lean.Omega"]

    def __init__(self, premises: List[Premise], imports: Dict[str, Set[str]], modules: List[str], filter: bool = True):
        self.premises: List[Premise] = []
        """All premises in corpus"""
        self.module_to_premises: Dict[str, List[str]] = {module: [] for module in modules}
        """A mapping from module name to premises inside module"""
        self.name2premise: Dict[str, Premise] = {}
        """Maps from premise name to `Premise`"""
        self.unfiltered_premises: List[Premise] = premises
        """The given list of premises during initialization before filtering to `self.premises`"""

        for premise in premises:
            if filter:
                if any(blacklisted in premise.module.split(".") for blacklisted in self.MODULE_BLACKLIST):
                    continue
                if any(blacklisted in premise.name.split(".") for blacklisted in self.NAME_BLACKLIST):
                    continue
                if any(premise.type.startswith(blacklisted) for blacklisted in self.TYPE_PREFIX_BLACKLIST):
                    continue
                if self.IS_PROP_FILTER and not premise.is_prop:
                    continue
            if premise.name in self.name2premise:
                # This happens in very rare cases; e.g. Subtype.ext_val_iff
                continue
            self.premises.append(premise)
            self.module_to_premises[premise.module].append(premise.name)
            self.name2premise[premise.name] = premise

        self.imports = imports
        """The (transitive) imports of each module"""
        self.modules = modules
        """Names of all modules"""

    def add_premise(self, premise: Premise):
        self.premises.append(premise)
        self.module_to_premises.setdefault(premise.module, []).append(premise.name)
        self.name2premise[premise.name] = premise
        self.unfiltered_premises.append(premise)
        if premise.module not in self.modules:
            self.modules.append(premise.module)
        # NOTE: in principle, self.imports should also be changed;
        # however, self.imports is not used by the server (which doesn't use the function `accessible_premises`)
        # and instead the client determines this set

    def accessible_premises(self, module: str, line: int, column: int, add_modules: Optional[Set[str]] = None) -> PremiseSet:
        """Get premises veisible to a location in source (unbundled version of get_accessible_premies)."""
        # Visible premises from imported modules
        imported_modules = self.imports[module].copy()
        if add_modules is not None:
            imported_modules.update(add_modules)
        imported_modules.discard(module)
        premises = PremiseSet(self, imported_modules)
        for name in self.module_to_premises[module]:
            premise = self.name2premise[name]
            if (premise.line, premise.column) <= (line, column):
                premises.add(premise)
        return premises

    def get_accessible_premises(self, state: State, add_modules: Optional[Set[str]] = None) -> PremiseSet:
        """Get the premises visible to a particular state in source code"""
        return self.accessible_premises(state.module, state.line, state.column, add_modules=add_modules)

    def get_accessible_negative_premises(self, state: StateWithTactic, add_modules: Optional[Set[str]] = None) -> PremiseSet:
        """Get the premises that are accessible but negative for a state"""
        # Get accessible premises
        premises = self.get_accessible_premises(state, add_modules=add_modules)
        # Remove positive premises
        for premise_name in state.hammer_recommendation:
            if premise_name in self.name2premise:
                premises.remove(self.name2premise[premise_name])
        # Also remove declaration itself
        if state.decl_name in self.name2premise:
            premises.remove(self.name2premise[state.decl_name])
        return premises

    # TODO decide whether to use this; not used at the moment
    def get_negative_premises(self, state: StateWithTactic) -> PremiseSet:
        """Get the premises that would be considered negative for the state"""
        # Also include premises that are unrelated to the state
        # not imported by state, nor imports state's module
        additional_modules = {
            module for module in self.imports
            if module != state.module and state.module not in self.imports[module]
        }
        return self.get_accessible_negative_premises(state, add_modules=additional_modules)

    @classmethod
    def from_ntp_toolkit(cls, base_dir: str, filter: bool = True, mathlib_only: bool = False):
        """Construct a `Corpus` of premises from `base_dir` of the ntp-toolkit outputs.
        If `filter`, filter out premises that are unlikely to be helpful for tactic generation.
        """
        blacklist_file = os.path.join(base_dir, "HammerBlacklist.jsonl")
        with open(blacklist_file) as f:
            blacklist = json.load(f)["hammerBlacklist"]

        premises: List[Premise] = []
        for module, i, premise_info in read_ntp_toolkit(os.path.join(base_dir, "Declarations")):
            if mathlib_only and not module.startswith("Mathlib."):
                continue
            premise = Premise.from_dict(module, i, premise_info)
            if premise.name in blacklist:
                continue
            premises.append(premise)

        imports: Dict[str, Set[str]] = {}
        for module, i, import_info in read_ntp_toolkit(os.path.join(base_dir, "Imports")):
            imports.setdefault(module, set()).add(import_info["name"])

        modules = list(read_ntp_toolkit_modules(os.path.join(base_dir, "Imports")))

        return cls(premises=premises, imports=imports, modules=modules, filter=filter)


def read_states(base_dir: str, mathlib_only: bool = False) -> List[StateWithTactic]:
    states: List[StateWithTactic] = []
    for module, i, state_info in read_ntp_toolkit(os.path.join(base_dir, "TrainingDataWithPremises")):
        if mathlib_only and not module.startswith("Mathlib."):
            continue
        state = StateWithTactic.from_dict(module, i, state_info)
        states.append(state)
    return states

# For testing
base_dir = "/data/user_data/thomaszh/Mathlib"
