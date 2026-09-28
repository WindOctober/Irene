"""Full-unitary adapters; never turn channel/partial-output tasks into unitary tasks."""
import json
import os
from pathlib import Path
import sys
import traceback

def prepare(case):
    if case['equivalence'] != 'unitary' or case.get('initial_state') == 'zero':
        raise NotImplementedError('tool adapter requires arbitrary-input full-unitary equivalence')
    from qiskit import QuantumCircuit, qasm2, qasm3, transpile
    circuits=[]
    names=[]
    for side in ('left','right'):
        text=Path(case[side+'_abs']).read_text()
        try:
            qc=qasm3.loads(text) if 'OPENQASM 3' in text else qasm2.loads(text, custom_instructions=qasm2.LEGACY_CUSTOM_INSTRUCTIONS)
        except Exception as e:
            raise NotImplementedError(f'Qiskit import: {e}') from e
        for item in qc.data:
            if item.operation.name in ('measure','reset','if_else','while_loop','for_loop','switch_case','store') or getattr(item.operation,'condition',None) is not None:
                raise NotImplementedError('nonunitary/control-flow operation in unitary adapter')
        names.append({f'quantum:{reg.name}[{i}]':qc.find_bit(q).index for reg in qc.qregs for i,q in enumerate(reg)})
        circuits.append(qc)
    n=circuits[0].num_qubits
    if circuits[1].num_qubits != n: raise NotImplementedError('unequal quantum interfaces')
    mappings=[]
    for key in ('input_pairs','output_pairs'):
        pairs=[pair.split('=') for pair in case.get(key,[])]
        if len(pairs)!=n or any(a not in names[0] or b not in names[1] for a,b in pairs):
            raise NotImplementedError('not a complete quantum interface mapping')
        mapping={names[1][b]:names[0][a] for a,b in pairs}
        if len(mapping)!=n or len(set(mapping.values()))!=n: raise NotImplementedError('nonbijective mapping')
        mappings.append(mapping)
    if mappings[0]!=mappings[1]: raise NotImplementedError('different input/output permutations')
    normalized=[]
    basis=['h','x','y','z','s','sdg','t','tdg','cx','ccx','rx','ry','rz']
    for side,qc in enumerate(circuits):
        # Numerical Qiskit lowering, no optimization; metadata records this policy.
        qc=transpile(qc,basis_gates=basis,optimization_level=0)
        out=QuantumCircuit(n)
        out.global_phase=qc.global_phase
        for item in qc.data:
            if item.operation.name=='barrier': continue
            if item.clbits or item.operation.name not in basis:
                raise NotImplementedError('unsupported operation after lowering')
            ids=[qc.find_bit(q).index for q in item.qubits]
            if side: ids=[mappings[0][i] for i in ids]
            out.append(item.operation,[out.qubits[i] for i in ids])
        normalized.append(out)
    return normalized

def main():
    tool,jobfile=sys.argv[1:3]
    case=json.loads(Path(jobfile).read_text())
    try:
        left,right=prepare(case)
        if tool=='quprs':
            from QuPRS import check_equivalence
            raw=check_equivalence(left,right,method='hybrid',backend='python',timeout=600).equivalent
            mapping={'equivalent':'eq','equivalent*':'eq','not_equivalent':'neq'}
            verdict=mapping.get(raw)
        else:
            from qiskit import qasm2
            import quokka_sharp as qk
            qasm2.dump(left,'left.qasm');qasm2.dump(right,'right.qasm')
            raw=qk.functionalities.eq('left.qasm','right.qasm',basis='comp',check='cyclic',N=1,epsilon=0)
            verdict='eq' if raw is True else 'neq' if raw is False else None
        status='completed'
        if str(raw).lower() in ('timeout','memout','memoryout'):
            status='timeout' if str(raw).lower()=='timeout' else 'memory_limit'
        result=dict(status=status,verdict=verdict or ('unknown' if status=='completed' else None),native_result=str(raw))
    except NotImplementedError as e: result=dict(status='unsupported',verdict=None,message=str(e))
    except MemoryError: result=dict(status='memory_limit',verdict=None)
    except Exception as e:
        traceback.print_exc()
        result=dict(status='error',verdict=None,message=str(e))
    print('RESULT_JSON='+json.dumps(result),flush=True)

if __name__=='__main__': main()
