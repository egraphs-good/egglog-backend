//! Mechanisms for declaring primitive types and functions on them.

use std::{
    any::{Any, TypeId},
    fmt::{self, Debug},
    hash::Hash,
    ops::Deref,
};

use numeric_id::{define_id, DenseIdMap, NumericId};

use crate::common::{HashMap, InternTable, Value};

#[cfg(test)]
mod tests;
mod unboxed;

define_id!(pub PrimitiveId, u32, "an identifier for primitive types");

/// A simple primitive type that can be interned in a database.
///
/// No one needs to implement this trait directly: any type with the trait requirements implements
/// it automatically.
pub trait Primitive: Clone + Hash + Eq + Any + Debug + Send + Sync {
    fn intern(&self, table: &InternTable<Self, Value>) -> Value {
        table.intern(self)
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl<T: Clone + Hash + Eq + Any + Debug + Send + Sync> Primitive for T {}

/// A wrapper used to print a primitive value.
///
/// The given primitive must be registered with the `Primitives` instance,
/// otherwise attempting to call the [`Debug`] implementation will panic.
pub struct PrimitivePrinter<'a> {
    pub prim: &'a Primitives,
    pub ty: PrimitiveId,
    pub val: Value,
}

impl Debug for PrimitivePrinter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.prim.tables[self.ty].print_value(self.val, f)
    }
}

/// A registry for primitive values and functions on them.
#[derive(Clone, Default)]
pub struct Primitives {
    type_ids: HashMap<TypeId, PrimitiveId>,
    tables: DenseIdMap<PrimitiveId, Box<dyn DynamicInternTable>>,
}

impl Primitives {
    /// Register the given type `P` as a primitive type in this registry.
    pub fn register_type<P: Primitive>(&mut self) -> PrimitiveId {
        let type_id = TypeId::of::<P>();
        let next_primitive_id = PrimitiveId::from_usize(self.type_ids.len());
        let id = *self.type_ids.entry(type_id).or_insert(next_primitive_id);
        self.tables
            .get_or_insert(id, || Box::<InternTable<P, Value>>::default());
        id
    }

    /// Get the [`PrimitiveId`] for the given primitive type `P`.
    pub fn get_ty<P: Primitive>(&self) -> PrimitiveId {
        self.type_ids[&TypeId::of::<P>()]
    }

    /// Get the [`PrimitiveId`] for the given primitive type id.
    pub fn get_ty_by_id(&self, id: TypeId) -> PrimitiveId {
        self.type_ids[&id]
    }

    /// Get a [`Value`] representing the given primitive `p`.
    pub fn get<P: Primitive>(&self, p: P) -> Value {
        let id = self.get_ty::<P>();
        let table = self.tables[id]
            .as_any()
            .downcast_ref::<InternTable<P, Value>>()
            .unwrap();
        p.intern(table)
    }

    /// Get a reference to the primitive value represented by the given [`Value`].
    fn unwrap_ref<P: Primitive>(&self, v: Value) -> impl Deref<Target = P> + '_ {
        let id = self.get_ty::<P>();
        let table = self
            .tables
            .get(id)
            .expect("types must be registered before unwrapping")
            .as_any()
            .downcast_ref::<InternTable<P, Value>>()
            .unwrap();
        table.get(v)
    }

    pub fn unwrap<P: Primitive>(&self, v: Value) -> P {
        self.unwrap_ref::<P>(v).clone()
    }
}

trait DynamicInternTable: Any + dyn_clone::DynClone + Send + Sync {
    fn as_any(&self) -> &dyn Any;
    fn print_value(&self, val: Value, f: &mut fmt::Formatter) -> fmt::Result;
}

// Implements `Clone` for `Box<dyn DynamicInternTable>`.
dyn_clone::clone_trait_object!(DynamicInternTable);

impl<P: Primitive> DynamicInternTable for InternTable<P, Value> {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn print_value(&self, val: Value, f: &mut fmt::Formatter) -> fmt::Result {
        let p = self.get(val);
        write!(f, "{:?}", &*p)
    }
}
