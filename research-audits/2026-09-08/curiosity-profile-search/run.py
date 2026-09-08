import json
from dataclasses import asdict
from pathlib import Path
from mikoshi_curiosity import (Concept, ConceptGraph, Conjecture, ResearchArchive,
    ResearchEvaluator, CompletenessCritic, CircularityCritic, KnownFailureCritic,
    LLMConjectureGenerator, OllamaProvider)

OUT = Path(__file__).parent
concepts = [
    Concept('labelled tensor space', 'R labelled copies of a d-dimensional space have dimension d^R, not binomial(R+d-1,d-1).'),
    Concept('orbit spans', 'Permutation-equivalent rows may jointly span the full space; one orbit is not one dimension.'),
    Concept('shared memory', 'Retaining an n-bit input supports arbitrarily many semantic observations; decoder runtime remains to be bounded.'),
    Concept('restricted positive result', 'Seek explicit sufficient conditions for a COMMON row space, and identify whether they apply to any real compiler.'),
]
seed = Conjecture(
    name='Repair labelled SPDP profile compression without assuming SAT hardness',
    statement='Propose three precise candidate lemmas repairing the gap from anonymous profiles to a common polynomial-dimensional labelled coefficient-row span. Include an explicit finite algebraic test for each. Do not claim P != NP. Prefer mathematically concrete restricted lemmas over an unsupported universal claim.',
    definitions=('SPDP rows are coefficient vectors of u times partial^tau p.', 'R is the number of labelled interfaces; d is a constant local dimension.', 'A valid separation also requires a proved universal compiler and rank-monotone hard-sheet extraction.'),
    assumptions=('Only explicit algebraic hypotheses are allowed.', 'No premise that all P machines have low SPDP rank or that SAT requires superpolynomial resources.', 'Per-row sparsity, orbit count, local arity and finite gate alphabet alone do not bound the joint span.'),
    proof_sketch=('State sufficient hypotheses.', 'Derive the dimension bound step by step.', 'Give a small counterexample when a key hypothesis is removed.', 'Explain exactly which hypothesis is not known for the general compiler.'),
    tags=('SPDP', 'labelled-span', 'SAT', 'repair'),
)
class RecordingProvider(OllamaProvider):
    def complete(self, prompt):
        (OUT / 'prompt.txt').write_text(prompt)
        answer = super().complete(prompt)
        (OUT / 'raw-response.json').write_text(answer)
        return answer

with ResearchArchive(OUT / 'archive.db') as archive:
    provider = RecordingProvider('qwen2:7b', timeout=240)
    generator = LLMConjectureGenerator(provider, failure_memory=archive)
    evaluator = ResearchEvaluator((CompletenessCritic(), CircularityCritic(), KnownFailureCritic()))
    print('Generating up to three new conjectures with local qwen2:7b via Curiosity.', flush=True)
    candidates = generator.generate(seed, concepts, 3)
    records = []
    for candidate in candidates:
        evaluation = evaluator.evaluate(candidate)
        archive.save(candidate, evaluation)
        records.append({'candidate': asdict(candidate), 'automated_evaluation': asdict(evaluation)})
    (OUT / 'candidates.json').write_text(json.dumps(records, indent=2))
    print(json.dumps(records, indent=2), flush=True)
