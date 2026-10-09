//! Exact affine output-support mismatch certificates; equality is inconclusive.
use super::*;
use bitgauss::BitMatrix;

/// Detects unequal affine output supports without evaluating amplitudes.
/// Joint (output, history) injectivity prevents cancellation between paths;
/// equal supports are inconclusive, not a proof of channel equality.
pub(super) fn compare(
    prepared: &PreparedComparison,
    kernel_terms: (usize, usize),
) -> Option<Analysis> {
    let left = exact_output_support(&prepared.left)?;
    let right = exact_output_support(&prepared.right)?;
    let witness =
        output_support_witness(&left, &right, prepared.left.quantum_input_positions.len())?;

    let mut analysis = Analysis::new(
        Verdict::NotEquivalent,
        Evidence::OutputSupportMismatch,
        kernel_terms,
    );
    analysis.counterexample = Some(Counterexample {
        ket_inputs: witness,
        bra_inputs: None,
    });
    Some(analysis)
}

struct ExactOutputSupport {
    width: usize,
    path_columns: Vec<Vec<bool>>,
    rank: usize,
    offset: Vec<bool>,
    input_columns: BTreeMap<Qubit, Vec<bool>>,
}

fn exact_output_support(side: &PreparedSide) -> Option<ExactOutputSupport> {
    let [component] = side.hps.components.as_slice() else {
        return None;
    };
    let [terminal] = side.terminals.as_slice() else {
        return None;
    };
    if !component.guard.is_empty() || !scalar_is_definitely_nonzero(&component.scalar) {
        return None;
    }
    let outputs = terminal
        .outputs
        .iter()
        .map(|output| &output.value)
        .collect::<Vec<_>>();
    if outputs.iter().any(|output| !output.is_affine()) {
        return None;
    }
    let history = component
        .output
        .history
        .iter()
        .map(HistoryEntry::value)
        .collect::<Vec<_>>();
    if history.iter().any(|value| !value.is_affine()) {
        return None;
    }

    let paths = component.path_support.iter().copied().collect::<Vec<_>>();
    let path_columns = paths
        .iter()
        .map(|path| coefficient_vector(&outputs, &Monomial::variable(Variable::Path(*path))))
        .collect::<Vec<_>>();
    let joint_columns = paths
        .iter()
        .map(|path| {
            let monomial = Monomial::variable(Variable::Path(*path));
            coefficient_vector(&outputs, &monomial)
                .into_iter()
                .chain(coefficient_vector(&history, &monomial))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    if column_rank(outputs.len() + history.len(), &joint_columns) != paths.len() {
        return None;
    }

    let inputs = outputs
        .iter()
        .flat_map(|output| output.variables())
        .filter_map(|variable| match variable {
            Variable::Input(qubit) => Some(qubit),
            Variable::Path(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let input_columns = inputs
        .into_iter()
        .map(|qubit| {
            let column = coefficient_vector(
                &outputs,
                &Monomial::variable(Variable::Input(qubit.clone())),
            );
            (qubit, column)
        })
        .collect();
    Some(ExactOutputSupport {
        width: outputs.len(),
        rank: column_rank(outputs.len(), &path_columns),
        path_columns,
        offset: coefficient_vector(&outputs, &Monomial::one()),
        input_columns,
    })
}

/// Returns a basis input whose two affine output-support cosets differ.
fn output_support_witness(
    left: &ExactOutputSupport,
    right: &ExactOutputSupport,
    input_count: usize,
) -> Option<Vec<bool>> {
    if left.rank != right.rank
        || column_rank(
            left.width,
            &left
                .path_columns
                .iter()
                .chain(&right.path_columns)
                .cloned()
                .collect::<Vec<_>>(),
        ) != left.rank
    {
        return Some(vec![false; input_count]);
    }

    let offset = xor_vectors(&left.offset, &right.offset);
    if !column_span_contains(left.width, &left.path_columns, left.rank, &offset) {
        return Some(vec![false; input_count]);
    }

    let inputs = left
        .input_columns
        .keys()
        .chain(right.input_columns.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    for input in inputs {
        let zero = vec![false; left.width];
        let difference = xor_vectors(
            left.input_columns.get(&input).unwrap_or(&zero),
            right.input_columns.get(&input).unwrap_or(&zero),
        );
        if !column_span_contains(left.width, &left.path_columns, left.rank, &difference) {
            let mut witness = vec![false; input_count];
            witness[input.index] = true;
            return Some(witness);
        }
    }
    None
}

fn coefficient_vector(outputs: &[&BooleanPolynomial], monomial: &Monomial) -> Vec<bool> {
    outputs
        .iter()
        .map(|output| {
            output
                .affine_coefficient(monomial)
                .expect("support check accepts only affine leaves")
        })
        .collect()
}

fn xor_vectors(left: &[bool], right: &[bool]) -> Vec<bool> {
    left.iter()
        .zip(right)
        .map(|(left, right)| left ^ right)
        .collect()
}

fn column_span_contains(width: usize, columns: &[Vec<bool>], rank: usize, value: &[bool]) -> bool {
    let mut extended = columns.to_vec();
    extended.push(value.to_vec());
    column_rank(width, &extended) == rank
}

fn column_rank(width: usize, columns: &[Vec<bool>]) -> usize {
    let mut matrix = BitMatrix::build(width, columns.len(), |row, column| columns[column][row]);
    matrix.gauss(false);
    (0..width)
        .filter(|row| (0..columns.len()).any(|column| matrix.bit(*row, column)))
        .count()
}

fn scalar_is_definitely_nonzero(scalar: &Scalar) -> bool {
    match scalar {
        Scalar::Rational(value) => value != &BigRational::from_integer(0.into()),
        Scalar::Sqrt(value) => {
            matches!(value.as_ref(), Scalar::Rational(value) if value > &BigRational::from_integer(0.into()))
        }
        Scalar::Mul(left, right) => {
            scalar_is_definitely_nonzero(left) && scalar_is_definitely_nonzero(right)
        }
        Scalar::Neg(value) | Scalar::Inverse(value) => scalar_is_definitely_nonzero(value),
        Scalar::Select {
            when_true,
            when_false,
            ..
        } => scalar_is_definitely_nonzero(when_true) && scalar_is_definitely_nonzero(when_false),
        Scalar::Sin(_) | Scalar::Cos(_) | Scalar::Add(_, _) => false,
    }
}
