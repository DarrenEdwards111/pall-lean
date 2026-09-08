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
    statement='Previous proposals failed: adding rows INCREASES rank and cannot prove an upper bound; repair functions were undefined. Propose TWO explicit restricted linear-algebra lemmas instead. Candidate direction A: rows individually invariant under all permutations of R tensor slots; bound their joint dimension. Candidate direction B: all rows lie in the image of ONE shared linear map from a D-dimensional vector space; bound their span. State exact inequalities, definitions and proofs, and state why the required hypotheses are NOT known for general SPDP compiler rows. Do not assume the compiler or SAT extraction, do not claim a separation, and do not introduce undefined repair functions. Keep each proof under 120 words.',
    definitions=('SPDP rows are coefficient vectors of u times partial^tau p.', 'R is the number of labelled interfaces; d is a constant local dimension.', 'A valid separation also requires a proved universal compiler and rank-monotone hard-sheet extraction.'),
    assumptions=('Only explicit algebraic hypotheses are allowed.', 'No premise that all P machines have low SPDP rank or that SAT requires superpolynomial resources.', 'Per-row sparsity, orbit count, local arity and finite gate alphabet alone do not bound the joint span.'),
    proof_sketch=('State sufficient hypotheses.', 'Derive the dimension bound step by step.', 'Give a small counterexample when a key hypothesis is removed.', 'Explain exactly which hypothesis is not known for the general compiler.'),
    tags=('SPDP', 'labelled-span', 'SAT', 'repair'),
)
class RecordingProvider(OllamaProvider):
    def complete(self, prompt):
        (OUT / 'round2-prompt.txt').write_text(prompt)
        answer = super().complete(prompt)
        (OUT / 'round2-raw-response.json').write_text(answer)
        return answer

with ResearchArchive(OUT / 'archive.db') as archive:
    provider = RecordingProvider('qwen2:7b', timeout=240)
    generator = LLMConjectureGenerator(provider, failure_memory=archive)
    evaluator = ResearchEvaluator((CompletenessCritic(), CircularityCritic(), KnownFailureCritic()))
    print('Generating up to three new conjectures with local qwen2:7b via Curiosity.', flush=True)
    candidates = generator.generate(seed, concepts, 2)
    records = []
    for candidate in candidates:
        evaluation = evaluator.evaluate(candidate)
        archive.save(candidate, evaluation)
        records.append({'candidate': asdict(candidate), 'automated_evaluation': asdict(evaluation)})
    (OUT / 'round2-candidates.json').write_text(json.dumps(records, indent=2))
    print(json.dumps(records, indent=2), flush=True)
