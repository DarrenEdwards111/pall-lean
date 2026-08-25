#!/usr/bin/env python3
"""Exhaust the normalized ordered three-term width-two selector frontier.

The model mirrors the executable Lean definitions used in
ComputationalDepthMultiSwitchingTwoSATBridge.lean: a gate is paired with its
termwise-negated polarity, and canonical DNF depth uses the first live literal
of the first active term.  The first audit reproduces the strict gap for
within-gate polarity concentration.  The second tests a pairwise refinement:
it counts fully-live clause pairs with a common signed literal and complementary
residual literals, breaking ties by polarity concentration.  The third audit
retains the missing two-coordinate interaction: such a pair contributes to its
shared coordinate when another fully-live clause contains the opposite sign of
that shared literal.  The fourth audit gives strict priority to the summed
decrease in active clause-support component count across the two immediate
Boolean children.  The fifth replaces raw component count by component support
excess above the target residual depth.  The sixth charges only whether each
component exceeds that depth.  The seventh and eighth retain both raw and
residual-aware component marginals, in the two possible fixed lexicographic
orders.  The final six audits add immediate terminal progress--the number of
indexed gates whose two query children both have canonical depth at most the
target--and test every fixed lexicographic order of terminal, raw, and excess
progress.  Only terminal-then-excess-then-raw clears the complete three-clause
bounded domain; the optional four-clause audit preserves its first strict gap.
The branch-balance audit then ranks a query by the smaller of the numbers of
shallow gates in its two immediate children, retaining terminal/excess/raw and
the signed motifs only as tie-breakers.  It clears the complete three-clause
domain and a reproducible bounded prefix of the four-clause domain.
The stored-tree comparison audit asks whether one new assignment can make a
freshly recomputed canonical tree more than one level deeper than the
corresponding restriction of the tree built at the parent.
All component audits inspect only the local
residual incidence graphs, not their stopping games.  Each audit stops at its
first strict gap against the exact flexible minimax game.
"""

import argparse
from functools import lru_cache
from itertools import combinations, permutations, product


N = 4
FUEL = 4
RESIDUAL_DEPTH = 1
LIVE = -1


def neg_gate(gate):
    return tuple(tuple((var, not sign) for var, sign in term) for term in gate)


def term_sat(term, rho):
    return all(rho[var] != LIVE and bool(rho[var]) == sign for var, sign in term)


def term_falsified(term, rho):
    return any(rho[var] != LIVE and bool(rho[var]) != sign for var, sign in term)


@lru_cache(maxsize=None)
def canonical_depth(gate, fuel, rho):
    if fuel == 0 or any(term_sat(term, rho) for term in gate):
        return 0
    active = next(
        (term for term in gate
         if not term_falsified(term, rho)
         and any(rho[var] == LIVE for var, _ in term)),
        None,
    )
    if active is None:
        return 0
    query = next(var for var, _ in active if rho[var] == LIVE)
    children = []
    for value in (0, 1):
        child = list(rho)
        child[query] = value
        children.append(canonical_depth(gate, fuel - 1, tuple(child)))
    return 1 + max(children)


@lru_cache(maxsize=None)
def canonical_tree(gate, fuel, rho):
    """Canonical tree with leaves represented by None and queries by triples."""
    if fuel == 0 or any(term_sat(term, rho) for term in gate):
        return None
    active = next(
        (term for term in gate
         if not term_falsified(term, rho)
         and any(rho[var] == LIVE for var, _ in term)),
        None,
    )
    if active is None:
        return None
    query = next(var for var, _ in active if rho[var] == LIVE)
    return (
        query,
        canonical_tree(gate, fuel - 1, fix(rho, query, 0)),
        canonical_tree(gate, fuel - 1, fix(rho, query, 1)),
    )


def restricted_tree_depth(tree, rho):
    if tree is None:
        return 0
    query, false_child, true_child = tree
    if rho[query] == 0:
        return restricted_tree_depth(false_child, rho)
    if rho[query] == 1:
        return restricted_tree_depth(true_child, rho)
    return 1 + max(
        restricted_tree_depth(false_child, fix(rho, query, 0)),
        restricted_tree_depth(true_child, fix(rho, query, 1)),
    )


def terminal(family, rho):
    return all(canonical_depth(gate, FUEL, rho) <= RESIDUAL_DEPTH for gate in family)


def fix(rho, query, value):
    child = list(rho)
    child[query] = value
    return tuple(child)


def concentration_profile(family, rho):
    scores = []
    for query in range(N):
        score = 0
        for gate in family:
            positive = 0
            negative = 0
            for term in gate:
                if all(rho[var] == LIVE for var, _ in term):
                    positive += any(var == query and sign for var, sign in term)
                    negative += any(var == query and not sign for var, sign in term)
            score += max(positive, negative)
        scores.append(score)
    return tuple(scores)


def selector_query(family, rho):
    live = [query for query in range(N) if rho[query] == LIVE]
    if not live:
        return None
    profile = concentration_profile(family, rho)
    best = max(profile[query] for query in live)
    return next(query for query in live if profile[query] == best)


def complementary_residual_pair_profile(family, rho):
    """Count signed-common-literal/complementary-residual pairs by residual variable."""
    scores = [0] * N
    for gate in family:
        fully_live = [
            term for term in gate
            if all(rho[var] == LIVE for var, _ in term)
        ]
        for left, right in combinations(fully_live, 2):
            left_set = set(left)
            right_set = set(right)
            shared = left_set & right_set
            if len(shared) != 1:
                continue
            left_residual = left_set - shared
            right_residual = right_set - shared
            if len(left_residual) != 1 or len(right_residual) != 1:
                continue
            (left_var, left_sign), = left_residual
            (right_var, right_sign), = right_residual
            if left_var == right_var and left_sign != right_sign:
                scores[left_var] += 1
    return tuple(scores)


def cancellation_certificate(family, rho):
    return (
        complementary_residual_pair_profile(family, rho),
        concentration_profile(family, rho),
    )


def cancellation_selector_query(family, rho):
    live = [query for query in range(N) if rho[query] == LIVE]
    if not live:
        return None
    pair_profile, concentration = cancellation_certificate(family, rho)
    return max(live, key=lambda query: (pair_profile[query], concentration[query], -query))


def externally_opposed_shared_pair_profile(family, rho):
    """Count cancellation pairs whose shared sign is opposed by another clause."""
    scores = [0] * N
    for gate in family:
        fully_live = [
            term for term in gate
            if all(rho[var] == LIVE for var, _ in term)
        ]
        for left_index, right_index in combinations(range(len(fully_live)), 2):
            left_set = set(fully_live[left_index])
            right_set = set(fully_live[right_index])
            shared = left_set & right_set
            if len(shared) != 1:
                continue
            left_residual = left_set - shared
            right_residual = right_set - shared
            if len(left_residual) != 1 or len(right_residual) != 1:
                continue
            (shared_var, shared_sign), = shared
            (left_var, left_sign), = left_residual
            (right_var, right_sign), = right_residual
            if left_var != right_var or left_sign == right_sign:
                continue
            if any(
                index not in (left_index, right_index)
                and (shared_var, not shared_sign) in term
                for index, term in enumerate(fully_live)
            ):
                scores[shared_var] += 1
    return tuple(scores)


def signed_two_coordinate_selector_query(family, rho):
    live = [query for query in range(N) if rho[query] == LIVE]
    if not live:
        return None
    external_profile = externally_opposed_shared_pair_profile(family, rho)
    pair_profile, concentration = cancellation_certificate(family, rho)
    return max(live, key=lambda query: (
        external_profile[query], pair_profile[query], concentration[query], -query
    ))


def active_clause_support_component_count(gate, rho):
    """Count components of active clauses joined by a shared live variable."""
    if any(term_sat(term, rho) for term in gate):
        return 0
    supports = [
        frozenset(var for var, _ in term if rho[var] == LIVE)
        for term in gate
        if not term_falsified(term, rho)
    ]
    supports = [support for support in supports if support]
    unseen = set(range(len(supports)))
    components = 0
    while unseen:
        components += 1
        frontier = [unseen.pop()]
        while frontier:
            left = frontier.pop()
            neighbors = {
                right for right in unseen if supports[left] & supports[right]
            }
            unseen.difference_update(neighbors)
            frontier.extend(neighbors)
    return components


def family_component_count(family, rho):
    return sum(active_clause_support_component_count(gate, rho) for gate in family)


def active_clause_support_component_excess(gate, rho):
    """Sum max(0, live-variable union size - target depth) by component."""
    if any(term_sat(term, rho) for term in gate):
        return 0
    supports = [
        frozenset(var for var, _ in term if rho[var] == LIVE)
        for term in gate
        if not term_falsified(term, rho)
    ]
    supports = [support for support in supports if support]
    unseen = set(range(len(supports)))
    excess = 0
    while unseen:
        seed = unseen.pop()
        variables = set(supports[seed])
        frontier = [seed]
        while frontier:
            left = frontier.pop()
            neighbors = {
                right for right in unseen if supports[left] & supports[right]
            }
            unseen.difference_update(neighbors)
            frontier.extend(neighbors)
            for right in neighbors:
                variables.update(supports[right])
        excess += max(0, len(variables) - RESIDUAL_DEPTH)
    return excess


def family_component_excess(family, rho):
    return sum(active_clause_support_component_excess(gate, rho) for gate in family)


def active_clause_support_unresolved_component_count(gate, rho):
    """Count components whose live-variable union exceeds the target depth."""
    if any(term_sat(term, rho) for term in gate):
        return 0
    supports = [
        frozenset(var for var, _ in term if rho[var] == LIVE)
        for term in gate
        if not term_falsified(term, rho)
    ]
    supports = [support for support in supports if support]
    unseen = set(range(len(supports)))
    unresolved = 0
    while unseen:
        seed = unseen.pop()
        variables = set(supports[seed])
        frontier = [seed]
        while frontier:
            left = frontier.pop()
            neighbors = {
                right for right in unseen if supports[left] & supports[right]
            }
            unseen.difference_update(neighbors)
            frontier.extend(neighbors)
            for right in neighbors:
                variables.update(supports[right])
        unresolved += len(variables) > RESIDUAL_DEPTH
    return unresolved


def family_unresolved_component_count(family, rho):
    return sum(
        active_clause_support_unresolved_component_count(gate, rho)
        for gate in family
    )


def component_marginal_profile(family, rho):
    """Summed two-child decrease, possibly negative when deletion splits support."""
    root_twice = 2 * family_component_count(family, rho)
    return tuple(
        root_twice
        - family_component_count(family, fix(rho, query, 0))
        - family_component_count(family, fix(rho, query, 1))
        if rho[query] == LIVE else 0
        for query in range(N)
    )


def component_aware_selector_query(family, rho):
    live = [query for query in range(N) if rho[query] == LIVE]
    if not live:
        return None
    component_profile = component_marginal_profile(family, rho)
    external_profile = externally_opposed_shared_pair_profile(family, rho)
    pair_profile, concentration = cancellation_certificate(family, rho)
    return max(live, key=lambda query: (
        component_profile[query], external_profile[query],
        pair_profile[query], concentration[query], -query
    ))


def component_excess_marginal_profile(family, rho):
    """Two-child decrease in residual-depth-aware component support excess."""
    root_twice = 2 * family_component_excess(family, rho)
    return tuple(
        root_twice
        - family_component_excess(family, fix(rho, query, 0))
        - family_component_excess(family, fix(rho, query, 1))
        if rho[query] == LIVE else 0
        for query in range(N)
    )


def component_excess_selector_query(family, rho):
    live = [query for query in range(N) if rho[query] == LIVE]
    if not live:
        return None
    excess_profile = component_excess_marginal_profile(family, rho)
    external_profile = externally_opposed_shared_pair_profile(family, rho)
    pair_profile, concentration = cancellation_certificate(family, rho)
    return max(live, key=lambda query: (
        excess_profile[query], external_profile[query],
        pair_profile[query], concentration[query], -query
    ))


def unresolved_component_marginal_profile(family, rho):
    root_twice = 2 * family_unresolved_component_count(family, rho)
    return tuple(
        root_twice
        - family_unresolved_component_count(family, fix(rho, query, 0))
        - family_unresolved_component_count(family, fix(rho, query, 1))
        if rho[query] == LIVE else 0
        for query in range(N)
    )


def unresolved_component_selector_query(family, rho):
    live = [query for query in range(N) if rho[query] == LIVE]
    if not live:
        return None
    unresolved_profile = unresolved_component_marginal_profile(family, rho)
    external_profile = externally_opposed_shared_pair_profile(family, rho)
    pair_profile, concentration = cancellation_certificate(family, rho)
    return max(live, key=lambda query: (
        unresolved_profile[query], external_profile[query],
        pair_profile[query], concentration[query], -query
    ))


def two_axis_component_selector_query(family, rho, raw_first):
    """Lexicographically rank both raw and residual-aware component progress."""
    live = [query for query in range(N) if rho[query] == LIVE]
    if not live:
        return None
    raw_profile = component_marginal_profile(family, rho)
    excess_profile = component_excess_marginal_profile(family, rho)
    external_profile = externally_opposed_shared_pair_profile(family, rho)
    pair_profile, concentration = cancellation_certificate(family, rho)

    def key(query):
        axes = ((raw_profile[query], excess_profile[query]) if raw_first else
                (excess_profile[query], raw_profile[query]))
        return axes + (
            external_profile[query], pair_profile[query],
            concentration[query], -query,
        )

    return max(live, key=key)


def raw_then_excess_selector_query(family, rho):
    return two_axis_component_selector_query(family, rho, True)


def excess_then_raw_selector_query(family, rho):
    return two_axis_component_selector_query(family, rho, False)


def immediate_terminal_progress_profile(family, rho):
    """Count gates made shallow in both immediate children by each live query."""
    return tuple(
        sum(
            canonical_depth(gate, FUEL, fix(rho, query, 0)) <= RESIDUAL_DEPTH
            and canonical_depth(gate, FUEL, fix(rho, query, 1)) <= RESIDUAL_DEPTH
            for gate in family
        ) if rho[query] == LIVE else 0
        for query in range(N)
    )


def branch_shallow_count_profile(family, rho):
    """Per query, count shallow gates separately in the false and true child."""
    return tuple(
        tuple(
            sum(
                canonical_depth(gate, FUEL, fix(rho, query, value))
                <= RESIDUAL_DEPTH
                for gate in family
            )
            for value in (0, 1)
        ) if rho[query] == LIVE else (0, 0)
        for query in range(N)
    )


def branch_balance_profile(family, rho):
    """Worst-child number of immediately shallow gates for every live query."""
    return tuple(min(counts) for counts in branch_shallow_count_profile(family, rho))


def branch_balance_selector_query(family, rho):
    """Prioritize worst-child shallow count, retaining the surviving scalar tie-breakers."""
    live = [query for query in range(N) if rho[query] == LIVE]
    if not live:
        return None
    balance = branch_balance_profile(family, rho)
    terminal = immediate_terminal_progress_profile(family, rho)
    excess = component_excess_marginal_profile(family, rho)
    raw = component_marginal_profile(family, rho)
    external_profile = externally_opposed_shared_pair_profile(family, rho)
    pair_profile, concentration = cancellation_certificate(family, rho)
    return max(live, key=lambda query: (
        balance[query], terminal[query], excess[query], raw[query],
        external_profile[query], pair_profile[query], concentration[query], -query,
    ))


def three_axis_component_selector_query(family, rho, axis_order):
    """Rank terminal progress, raw marginal, and excess marginal in a fixed order."""
    live = [query for query in range(N) if rho[query] == LIVE]
    if not live:
        return None
    profiles = {
        "terminal": immediate_terminal_progress_profile(family, rho),
        "raw": component_marginal_profile(family, rho),
        "excess": component_excess_marginal_profile(family, rho),
    }
    external_profile = externally_opposed_shared_pair_profile(family, rho)
    pair_profile, concentration = cancellation_certificate(family, rho)
    return max(live, key=lambda query: tuple(
        profiles[axis][query] for axis in axis_order
    ) + (
        external_profile[query], pair_profile[query],
        concentration[query], -query,
    ))


def three_axis_selector(axis_order):
    return lambda family, rho: three_axis_component_selector_query(
        family, rho, axis_order
    )


def costs(family, query_rule=selector_query):
    @lru_cache(maxsize=None)
    def flexible(rho):
        if terminal(family, rho):
            return 0
        live = [query for query in range(N) if rho[query] == LIVE]
        return 1 + min(
            max(flexible(fix(rho, query, 0)), flexible(fix(rho, query, 1)))
            for query in live
        )

    @lru_cache(maxsize=None)
    def selected(rho):
        if terminal(family, rho):
            return 0
        query = query_rule(family, rho)
        assert query is not None
        return 1 + max(selected(fix(rho, query, 0)), selected(fix(rho, query, 1)))

    return flexible, selected


def show_gate(gate):
    return "[" + ", ".join(
        "(" + ", ".join(("" if sign else "not ") + str(var) for var, sign in term) + ")"
        for term in gate
    ) + "]"


def normalized_ordered_gates(term_count=3):
    """Generate the audit domain; literal and clause order affect canonical walks."""
    terms = [
        ((left, left_sign), (right, right_sign))
        for left in range(N)
        for right in range(N)
        if left != right
        for left_sign, right_sign in product((False, True), repeat=2)
    ]
    return permutations(terms, term_count)


def first_shallow_count_monotonicity_gap(term_count=3):
    """Find a shallow canonical gate made deep by one further variable assignment."""
    restrictions = list(product((LIVE, 0, 1), repeat=N))
    checked_gates = 0
    checked_extensions = 0
    for gate in normalized_ordered_gates(term_count):
        if len(set(gate)) != term_count:
            continue
        canonical_depth.cache_clear()
        checked_gates += 1
        for rho in restrictions:
            if canonical_depth(gate, FUEL, rho) > RESIDUAL_DEPTH:
                continue
            for query in range(N):
                if rho[query] != LIVE:
                    continue
                for value in (0, 1):
                    checked_extensions += 1
                    child = fix(rho, query, value)
                    child_depth = canonical_depth(gate, FUEL, child)
                    if child_depth > RESIDUAL_DEPTH:
                        return {
                            "gate": gate,
                            "restriction": rho,
                            "root_depth": canonical_depth(gate, FUEL, rho),
                            "query": query,
                            "value": value,
                            "child_depth": child_depth,
                            "checked_gates": checked_gates,
                            "checked_extensions": checked_extensions,
                        }
    return {
        "checked_gates": checked_gates,
        "checked_extensions": checked_extensions,
    }


def first_stored_tree_additive_gap(term_count=3, max_gates=None):
    """Refute recomputed depth <= stored residual depth + one new fixing."""
    restrictions = list(product((LIVE, 0, 1), repeat=N))
    checked_gates = 0
    checked_extensions = 0
    for gate in normalized_ordered_gates(term_count):
        if len(set(gate)) != term_count:
            continue
        canonical_depth.cache_clear()
        canonical_tree.cache_clear()
        checked_gates += 1
        if max_gates is not None and checked_gates > max_gates:
            return {
                "checked_gates": checked_gates - 1,
                "checked_extensions": checked_extensions,
                "truncated": True,
            }
        for rho in restrictions:
            stored = canonical_tree(gate, FUEL, rho)
            for query in range(N):
                if rho[query] != LIVE:
                    continue
                for value in (0, 1):
                    checked_extensions += 1
                    child = fix(rho, query, value)
                    stored_depth = restricted_tree_depth(stored, child)
                    recomputed_depth = canonical_depth(gate, FUEL, child)
                    if recomputed_depth > stored_depth + 1:
                        return {
                            "gate": gate,
                            "restriction": rho,
                            "root_depth": canonical_depth(gate, FUEL, rho),
                            "query": query,
                            "value": value,
                            "stored_depth": stored_depth,
                            "recomputed_depth": recomputed_depth,
                            "checked_gates": checked_gates,
                            "checked_extensions": checked_extensions,
                        }
    return {
        "checked_gates": checked_gates,
        "checked_extensions": checked_extensions,
    }


def stacked_distraction_instance(distractions):
    """Scalable normalized witness with one guard, distractions, and one terminal clause."""
    terminal = distractions + 2
    gate = (
        (((0, False), (1, False)),)
        + tuple(((query + 2, False), (0, False)) for query in range(distractions))
        + (((0, False), (terminal, False)),)
    )
    rho = tuple(0 if query == terminal else LIVE for query in range(distractions + 3))
    tau = fix(rho, 1, 1)
    return gate, rho, tau


def audit_stacked_distraction_family(max_distractions):
    """Check the exact stored/fresh depths for every size through the requested bound."""
    rows = []
    for distractions in range(max_distractions + 1):
        gate, rho, tau = stacked_distraction_instance(distractions)
        fuel = distractions + 3
        stored = canonical_tree(gate, fuel, rho)
        stored_depth = restricted_tree_depth(stored, tau)
        recomputed_depth = canonical_depth(gate, fuel, tau)
        normalized = len(set(gate)) == len(gate) and all(
            len({var for var, _ in term}) == len(term) for term in gate
        )
        expected = (stored_depth == 1 and recomputed_depth == distractions + 1)
        if not normalized or not expected:
            raise AssertionError({
                "distractions": distractions,
                "normalized": normalized,
                "stored_depth": stored_depth,
                "recomputed_depth": recomputed_depth,
            })
        rows.append((distractions, stored_depth, recomputed_depth))
    return rows


def show_stacked_distraction_audit(rows):
    print("parameterized stacked-distraction audit")
    print("checked sizes:", len(rows))
    print("largest distraction count:", rows[-1][0])
    print("largest stored residual depth:", rows[-1][1])
    print("largest recomputed depth:", rows[-1][2])


def show_shallow_count_monotonicity_gap(gap):
    print("canonical shallow-count monotonicity audit")
    if "gate" not in gap:
        print("no monotonicity gap")
    else:
        print("first monotonicity gap")
        print("gate:", show_gate(gap["gate"]))
        print("restriction:", gap["restriction"])
        print("root depth:", gap["root_depth"])
        print("extension:", (gap["query"], gap["value"]))
        print("child depth:", gap["child_depth"])
    print("checked gates:", gap["checked_gates"])
    print("checked extensions:", gap["checked_extensions"])


def show_stored_tree_additive_gap(gap):
    print("stored-tree additive-one comparison audit")
    if "gate" not in gap:
        if gap.get("truncated"):
            print("no additive-one gap in bounded prefix")
        else:
            print("no additive-one gap")
    else:
        print("first additive-one gap")
        print("gate:", show_gate(gap["gate"]))
        print("restriction:", gap["restriction"])
        print("root depth:", gap["root_depth"])
        print("extension:", (gap["query"], gap["value"]))
        print("stored residual depth:", gap["stored_depth"])
        print("recomputed depth:", gap["recomputed_depth"])
    print("checked gates:", gap["checked_gates"])
    print("checked extensions:", gap["checked_extensions"])


def first_gap(query_rule, term_count=3, max_gates=None):
    restrictions = list(product((LIVE, 0, 1), repeat=N))
    checked_gates = 0
    checked_states = 0
    for gate in normalized_ordered_gates(term_count):
        # Lean's `List.Nodup` normalization condition is syntactic.
        if len(set(gate)) != term_count:
            continue
        # Canonical-depth keys include the entire ordered gate.  Retaining keys from every
        # earlier gate makes a complete no-gap audit consume memory without enabling reuse.
        canonical_depth.cache_clear()
        family = (gate, neg_gate(gate))
        flexible, selected = costs(family, query_rule)
        checked_gates += 1
        if max_gates is not None and checked_gates > max_gates:
            return {
                "checked_gates": checked_gates - 1,
                "checked_states": checked_states,
                "truncated": True,
            }
        for rho in restrictions:
            checked_states += 1
            optimum = flexible(rho)
            selector = selected(rho)
            if selector > optimum:
                winning = tuple(
                    query for query in range(N) if rho[query] == LIVE
                    and 1 + max(
                        flexible(fix(rho, query, 0)),
                        flexible(fix(rho, query, 1)),
                    ) == optimum
                )
                return {
                    "gate": gate,
                    "family": family,
                    "restriction": rho,
                    "selected_query": query_rule(family, rho),
                    "winning_queries": winning,
                    "flexible_cost": optimum,
                    "selector_cost": selector,
                    "checked_gates": checked_gates,
                    "checked_states": checked_states,
                }
    return {"checked_gates": checked_gates, "checked_states": checked_states}


def show_gap(label, gap):
    print(label)
    if "gate" not in gap:
        if gap.get("truncated"):
            print("no strict gap in bounded prefix")
        else:
            print("no strict gap")
    else:
        print("first strict gap")
        print("gate:", show_gate(gap["gate"]))
        print("restriction:", gap["restriction"])
        print("concentration profile:", concentration_profile(
            gap["family"], gap["restriction"]))
        print("complementary residual-pair profile:",
              complementary_residual_pair_profile(
                  gap["family"], gap["restriction"]))
        print("externally opposed shared-pair profile:",
              externally_opposed_shared_pair_profile(
                  gap["family"], gap["restriction"]))
        print("component marginal profile:",
              component_marginal_profile(gap["family"], gap["restriction"]))
        print("component excess marginal profile:",
              component_excess_marginal_profile(
                  gap["family"], gap["restriction"]))
        print("unresolved component marginal profile:",
              unresolved_component_marginal_profile(
                  gap["family"], gap["restriction"]))
        print("immediate terminal-progress profile:",
              immediate_terminal_progress_profile(
                  gap["family"], gap["restriction"]))
        print("branch shallow-count profile:",
              branch_shallow_count_profile(gap["family"], gap["restriction"]))
        print("branch-balance profile:",
              branch_balance_profile(gap["family"], gap["restriction"]))
        print("selected query:", gap["selected_query"])
        print("winning queries:", gap["winning_queries"])
        print("flexible cost:", gap["flexible_cost"])
        print("selector cost:", gap["selector_cost"])
    print("checked gates:", gap["checked_gates"])
    print("checked states:", gap["checked_states"])


def three_clause_audits():
    show_gap("polarity concentration audit", first_gap(selector_query))
    print()
    show_gap("complementary residual-pair audit",
             first_gap(cancellation_selector_query))
    print()
    show_gap("signed two-coordinate motif audit",
             first_gap(signed_two_coordinate_selector_query))
    print()
    show_gap("component-aware motif audit",
             first_gap(component_aware_selector_query))
    print()
    show_gap("residual-depth-aware component excess audit",
             first_gap(component_excess_selector_query))
    print()
    show_gap("unresolved component count audit",
             first_gap(unresolved_component_selector_query))
    print()
    show_gap("raw-then-excess two-axis component audit",
             first_gap(raw_then_excess_selector_query))
    print()
    show_gap("excess-then-raw two-axis component audit",
             first_gap(excess_then_raw_selector_query))
    print()
    axis_orders = (
        ("terminal", "raw", "excess"),
        ("terminal", "excess", "raw"),
        ("raw", "terminal", "excess"),
        ("raw", "excess", "terminal"),
        ("excess", "terminal", "raw"),
        ("excess", "raw", "terminal"),
    )
    for axis_order in axis_orders:
        print()
        show_gap(
            "-then-".join(axis_order) + " three-axis component audit",
            first_gap(three_axis_selector(axis_order)),
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--four-clause-survivor",
        action="store_true",
        help=("audit only terminal-then-excess-then-raw on ordered four-clause "
              "gates"),
    )
    parser.add_argument(
        "--max-gates",
        type=int,
        help="stop a four-clause audit after this many ordered gates",
    )
    parser.add_argument(
        "--branch-balance",
        action="store_true",
        help="audit only the worst-child shallow-gate selector",
    )
    parser.add_argument(
        "--shallow-monotonicity",
        action="store_true",
        help="find a shallow gate made deep by extending its restriction",
    )
    parser.add_argument(
        "--stored-tree-comparison",
        action="store_true",
        help="test the additive-one stored-tree/recomputed-depth comparison",
    )
    parser.add_argument(
        "--stacked-distraction",
        type=int,
        metavar="MAX",
        help="check the parameterized stacked witness for every size from zero through MAX",
    )
    args = parser.parse_args()
    if args.stacked_distraction is not None:
        if args.stacked_distraction < 0:
            parser.error("--stacked-distraction must be nonnegative")
        show_stacked_distraction_audit(
            audit_stacked_distraction_family(args.stacked_distraction)
        )
    elif args.stored_tree_comparison:
        show_stored_tree_additive_gap(
            first_stored_tree_additive_gap(
                term_count=4 if args.four_clause_survivor else 3,
                max_gates=args.max_gates,
            )
        )
    elif args.shallow_monotonicity:
        show_shallow_count_monotonicity_gap(
            first_shallow_count_monotonicity_gap()
        )
    elif args.branch_balance:
        show_gap(
            "branch-balanced shallow-gate audit",
            first_gap(
                branch_balance_selector_query,
                term_count=4 if args.four_clause_survivor else 3,
                max_gates=args.max_gates,
            ),
        )
    elif args.four_clause_survivor:
        show_gap(
            "four-clause terminal-then-excess-then-raw audit",
            first_gap(
                three_axis_selector(("terminal", "excess", "raw")),
                term_count=4,
                max_gates=args.max_gates,
            ),
        )
    else:
        three_clause_audits()


if __name__ == "__main__":
    main()
