import unittest

from import_itertestq import static_interface
from materialize_caqr import measured_mapping

HEADER = 'OPENQASM 2.0;\ninclude "qelib1.inc";\nqreg q[2];\ncreg c[2];\n'


class Interfaces(unittest.TestCase):
    def test_static_and_comments(self):
        self.assertEqual(static_interface(HEADER + '// measure q[0];\nh q[0];'),
                         ['quantum:q[0]', 'quantum:q[1]'])

    def test_nonunitary_rejected(self):
        for statement in ('measure q[0] -> c[0];', 'reset q[0];', 'if(c==1) x q[0];'):
            with self.assertRaisesRegex(ValueError, 'nonunitary'):
                static_interface(HEADER + statement)

    def test_reused_wire_is_not_same_index(self):
        left = HEADER + 'measure q[0] -> c[0]; measure q[1] -> c[1];'
        right = HEADER + 'measure q[0] -> c[1]; reset q[0]; measure q[0] -> c[0];'
        pairs, _ = measured_mapping(left, right, [[0, 1]])
        self.assertEqual(pairs, ['classical:c[0]=classical:c[1]', 'classical:c[1]=classical:c[0]'])

    def test_overwritten_output_rejected(self):
        left = HEADER + 'measure q[0] -> c[0]; measure q[1] -> c[1];'
        right = HEADER + 'measure q[0] -> c[0]; reset q[0]; measure q[0] -> c[0];'
        with self.assertRaisesRegex(ValueError, 'overwritten'):
            measured_mapping(left, right, [[0, 1]])

    def test_incomplete_chain_rejected(self):
        source = HEADER + 'measure q[0] -> c[0];'
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            measured_mapping(source, source, [[0, 1]])

    def test_no_classical_observables_rejected(self):
        with self.assertRaisesRegex(ValueError, 'no_original_classical'):
            measured_mapping(HEADER, HEADER, [[0, 1]])


if __name__ == '__main__':
    unittest.main()
