use super::{PrimitivePrinter, Primitives};

#[test]
fn prim_printing() {
    let mut prims = Primitives::default();
    prims.register_type::<i64>();
    let ty = prims.get_ty::<i64>();
    let val = prims.get(24i64);
    assert_eq!(
        format!(
            "{:?}",
            PrimitivePrinter {
                prim: &prims,
                ty,
                val
            }
        ),
        "24"
    );
}
