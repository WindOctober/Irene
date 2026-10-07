//! Owned FLINT/Arb storage and outward-rounded matrix norm bounds.
//!
//! No approximate (`acb_*_approx`) entry points are used. All raw allocations
//! stay here; initialized entries have one owner and indices are checked before
//! crossing FFI. Rug and FLINT use the same Cargo-linked GMP/MPFR library.
#![deny(clippy::undocumented_unsafe_blocks)]
use super::*;
use flint_sys::{acb::*, acb_types::acb_struct, arb::*, arb_types::mag_struct, mag::*};
use std::ptr::NonNull;

pub(super) struct Magnitude(mag_struct);

impl Magnitude {
    pub fn zero() -> Self {
        let mut value = mag_struct::default();
        // SAFETY: initialize uniquely owned storage, cleared by Drop.
        unsafe { mag_init(&mut value) };
        Self(value)
    }

    pub fn add_assign(&mut self, other: &Self) {
        // SAFETY: initialized operands; mag_add supports aliasing.
        unsafe { mag_add(&mut self.0, &self.0, &other.0) };
    }

    fn max_assign(&mut self, other: &Self) {
        // SAFETY: initialized operands; mag_max supports aliasing.
        unsafe { mag_max(&mut self.0, &self.0, &other.0) };
    }

    pub fn twice_rational(&self) -> Option<BigRational> {
        let mut value = Balls::new(1);
        // Interval [-radius, radius], converted outward through MPFR. Avoid a
        // floating conversion that could underflow a tiny positive error to 0.
        // SAFETY: initialized destination and read-only initialized magnitude.
        unsafe { acb_add_error_mag(value.at_mut(0), &self.0) };
        let upper = value.enclosure(0)?.re.hi;
        Some(float_rational(&upper)? * BigRational::from_integer(2.into()))
    }
}

impl Drop for Magnitude {
    fn drop(&mut self) {
        // SAFETY: one initialized magnitude, no shallow copies.
        unsafe { mag_clear(&mut self.0) };
    }
}

/// ||A||_2 <= sqrt(||A||_1 ||A||_inf), using nonnegative entry bounds.
pub(super) struct Norm {
    rows: Vec<Magnitude>,
    cols: Vec<Magnitude>,
}

impl Norm {
    pub fn new(dimension: usize) -> Self {
        Self {
            rows: (0..dimension).map(|_| Magnitude::zero()).collect(),
            cols: (0..dimension).map(|_| Magnitude::zero()).collect(),
        }
    }

    pub fn add_radius(&mut self, row: usize, col: usize, values: &Balls, at: usize) {
        let mut radius = Magnitude::zero();
        // SAFETY: at() checks bounds; read-only initialized Arb entries.
        unsafe {
            let value = &*values.at(at);
            mag_hypot(&mut radius.0, &value.real.rad, &value.imag.rad);
        }
        self.add(row, col, &radius);
    }

    fn add_value(&mut self, row: usize, col: usize, values: &Balls, at: usize) {
        let mut magnitude = Magnitude::zero();
        // SAFETY: initialized output and checked input; upward magnitude bound.
        unsafe { acb_get_mag(&mut magnitude.0, values.at(at)) };
        self.add(row, col, &magnitude);
    }

    fn add(&mut self, row: usize, col: usize, magnitude: &Magnitude) {
        self.rows[row].add_assign(magnitude);
        self.cols[col].add_assign(magnitude);
    }

    pub fn bound(&self) -> Magnitude {
        let mut row = Magnitude::zero();
        let mut col = Magnitude::zero();
        for r in &self.rows {
            row.max_assign(r);
        }
        for c in &self.cols {
            col.max_assign(c);
        }
        // SAFETY: all magnitudes initialized; both operations round upward.
        unsafe {
            mag_mul(&mut row.0, &row.0, &col.0);
            mag_sqrt(&mut row.0, &row.0);
        }
        row
    }
}

pub(super) struct Balls {
    ptr: NonNull<acb_struct>,
    len: usize,
}

impl Balls {
    pub fn new(len: usize) -> Self {
        assert!(len > 0 && len <= isize::MAX as usize);
        // SAFETY: FLINT initializes len zero entries, paired with vec_clear.
        let ptr = NonNull::new(unsafe { _acb_vec_init(len as _) }).expect("Arb allocation");
        Self { ptr, len }
    }

    fn at(&self, i: usize) -> *const acb_struct {
        assert!(i < self.len);
        // SAFETY: in-bounds entry in the allocation owned by self.
        unsafe { self.ptr.as_ptr().add(i) }
    }

    fn at_mut(&mut self, i: usize) -> *mut acb_struct {
        self.at(i).cast_mut()
    }

    pub fn one(&mut self, i: usize) {
        // SAFETY: checked index into uniquely owned, initialized storage.
        unsafe { acb_one(self.at_mut(i)) };
    }

    pub fn is_one(&self, i: usize) -> bool {
        // SAFETY: checked read-only initialized entry.
        unsafe { acb_is_one(self.at(i)) != 0 }
    }

    pub fn set_enclosure(&mut self, i: usize, value: &Complex, precision: u32) {
        // SAFETY: both bindings use the same MPFR ABI; read-only endpoints
        // remain alive for the call, destination is uniquely owned.
        unsafe {
            let target = &mut *self.at_mut(i);
            arb_set_interval_mpfr(
                &mut target.real,
                value.re.lo.as_raw().cast(),
                value.re.hi.as_raw().cast(),
                precision.into(),
            );
            arb_set_interval_mpfr(
                &mut target.imag,
                value.im.lo.as_raw().cast(),
                value.im.hi.as_raw().cast(),
                precision.into(),
            );
        }
    }

    pub fn enclosure(&self, i: usize) -> Option<Complex> {
        let mut result = Complex::n(0);
        // SAFETY: MPFR endpoints are initialized and individually writable.
        unsafe {
            let value = self.at(i);
            if acb_is_finite(value) == 0 {
                return None;
            }
            arb_get_interval_mpfr(
                result.re.lo.as_raw_mut().cast(),
                result.re.hi.as_raw_mut().cast(),
                &(*value).real,
            );
            arb_get_interval_mpfr(
                result.im.lo.as_raw_mut().cast(),
                result.im.hi.as_raw_mut().cast(),
                &(*value).imag,
            );
        }
        Some(result)
    }

    pub fn swap(&mut self, a: usize, b: usize) {
        // SAFETY: checked owned entries; FLINT permits self-swap.
        unsafe { acb_swap(self.at_mut(a), self.at_mut(b)) };
    }

    pub fn swap_from(&mut self, i: usize, other: &mut Self, j: usize) {
        // SAFETY: checked initialized entries of two disjoint owned vectors.
        unsafe { acb_swap(self.at_mut(i), other.at_mut(j)) };
    }

    pub fn midpoint(&mut self, i: usize) {
        // Only after recording the discarded radius in the operator error.
        // SAFETY: checked initialized entry; acb_get_mid permits aliasing.
        unsafe { acb_get_mid(self.at_mut(i), self.at(i)) };
    }

    pub fn multiply(&mut self, i: usize, coefficient: &Self, j: usize, precision: u32) {
        // SAFETY: checked initialized entries; acb_mul permits output aliasing.
        unsafe {
            acb_mul(
                self.at_mut(i),
                self.at(i),
                coefficient.at(j),
                precision.into(),
            )
        };
    }

    pub fn sum_products(
        &mut self,
        output: usize,
        inputs: &Self,
        coefficients: &Self,
        indices: impl Iterator<Item = usize>,
        precision: u32,
    ) {
        if coefficients.len == 2 {
            let mut indices = indices;
            let a = indices.next().expect("two dot-product inputs");
            let b = indices.next().expect("two dot-product inputs");
            assert!(indices.next().is_none(), "two dot-product inputs");
            let first = inputs.at(a);
            let _last = inputs.at(b);
            // Most local blocks have exactly two terms per output. Accumulate
            // them together with rigorous rounding instead of two addmul calls.
            // Balls allocations fit isize, so the signed stride also fits.
            let stride = b as isize - a as isize;
            // SAFETY: both strided endpoints and both coefficients are checked
            // initialized entries. Scratch output is disjoint from the inputs;
            // acb_dot allows negative/zero strides and retains error bounds.
            unsafe {
                acb_dot(
                    self.at_mut(output),
                    std::ptr::null(),
                    0,
                    first,
                    stride.try_into().expect("FLINT input stride"),
                    coefficients.at(0),
                    1,
                    2,
                    precision.into(),
                )
            };
            return;
        }
        // SAFETY: checked index into uniquely owned, initialized storage.
        unsafe { acb_zero(self.at_mut(output)) };
        for (j, i) in indices.enumerate() {
            // SAFETY: disjoint output and immutable inputs, checked indices.
            unsafe {
                acb_addmul(
                    self.at_mut(output),
                    inputs.at(i),
                    coefficients.at(j),
                    precision.into(),
                )
            };
        }
    }

    pub fn certificates(
        &self,
        dimension: usize,
        error: &Magnitude,
        precision: u32,
    ) -> Option<(BigRational, BigRational)> {
        assert_eq!(self.len, dimension * dimension);
        let mut trace = Self::new(1);
        for i in 0..dimension {
            // SAFETY: checked initialized entries; acb_add permits aliasing.
            unsafe {
                acb_add(
                    trace.at_mut(0),
                    trace.at(0),
                    self.at(i * dimension + i),
                    precision.into(),
                )
            };
        }
        // Pick ONE exact unit-modulus phase: z/|z| for the exact midpoint z
        // of the computed trace. The ball encloses that phase, not an arbitrary
        // normalization of an uncertain trace. Zero midpoint uses phase 1.
        let mut phase = Self::new(1);
        // SAFETY: checked initialized entries; midpoint and sign support aliasing.
        unsafe {
            acb_get_mid(phase.at_mut(0), trace.at(0));
            if acb_is_zero(phase.at(0)) != 0 {
                acb_one(phase.at_mut(0));
            } else {
                acb_sgn(phase.at_mut(0), phase.at(0), precision.into());
            }
        }
        let mut residual = Norm::new(dimension);
        let mut entry = Self::new(1);
        for row in 0..dimension {
            for col in 0..dimension {
                if row == col {
                    // SAFETY: checked initialized inputs and disjoint scratch.
                    unsafe {
                        acb_sub(
                            entry.at_mut(0),
                            self.at(row * dimension + col),
                            phase.at(0),
                            precision.into(),
                        )
                    };
                    residual.add_value(row, col, &entry, 0);
                } else {
                    residual.add_value(row, col, self, row * dimension + col);
                }
            }
        }
        let mut residual_bound = residual.bound();
        residual_bound.add_assign(error);
        let residual_upper = residual_bound
            .twice_rational()?
            .min(BigRational::from_integer(2.into()));
        // |Tr(U-M)/d| <= ||U-M||_2. The rectangle +/-error on BOTH axes
        // contains the disk, so existing trace lower/upper bounds remain sound.
        // SAFETY: nonzero dimension; initialized operands with supported aliasing.
        unsafe {
            acb_div_ui(
                trace.at_mut(0),
                trace.at(0),
                dimension as _,
                precision.into(),
            );
            acb_add_error_mag(trace.at_mut(0), &error.0);
        }
        let (trace_upper, lower) = trace_bounds(&trace.enclosure(0)?, dimension.ilog2() as usize)?;
        Some((residual_upper.min(trace_upper), lower))
    }
}

impl Drop for Balls {
    fn drop(&mut self) {
        // SAFETY: free exactly the initialized allocation, once.
        unsafe { _acb_vec_clear(self.ptr.as_ptr(), self.len as _) };
    }
}
