#!/usr/bin/env python3
"""Machine-read final #print axioms output; NOT a check of semantic sufficiency."""
import re, sys
report=open(sys.argv[1],encoding='utf-8').read()
permitted={'propext','Classical.choice','Quot.sound'}
required=['TPCV9StatementAudit.actual_tpc_statement_matches_Nat_Prime',
          'TwinPrimeCurrentCertification.current_source_implies_tpc',
          'TwinPrimeCurrentCertification.published_weil_to_turn397_kernel_bound',
          'TP132V9WeilCRT.exact_crt_factorization_at_v9_prime_modulus',
          'TP132V9BVRange.v9_typeII_exponent_strictly_sublinear']
fail=[]
for name in required:
    # Lean emits: 'NAME' depends on axioms: [propext, Classical.choice, Quot.sound]
    pattern=r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]"
    found=re.search(pattern, report, re.S)
    if not found:
        empty = re.search(r"'"+re.escape(name)+r"' does not depend on any axioms", report)
        if empty:
            continue
        fail.append('No parseable #print axioms for '+name)
        continue
    names={a.strip() for a in found.group(1).split(',') if a.strip()}
    extras=names-permitted
    if extras: fail.append('Non-standard axioms in '+name+': '+', '.join(sorted(extras)))
if fail:
    print('AXIOM AUDIT INCOMPLETE/FAILED:')
    print('\n'.join(fail)); sys.exit(1)
print('PASS: named theorem declarations depend only on standard axioms.')
