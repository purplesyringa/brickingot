use noak::{
    descriptor::{BaseType, MethodDescriptor, TypeDescriptor},
    error::DecodeError,
    reader::{
        Class,
        cpool::{Index, NameAndType},
    },
};
use rustc_hash::FxHashMap;
use std::collections::hash_map::Entry;

// Acts as a repository of information cached for a class to optimize method decompilation.
pub struct ClassInfo<'code> {
    class: &'code Class<'code>,
    method_descriptors: FxHashMap<Index<NameAndType<'code>>, MethodDescriptorInfo<'code>>,
}

pub struct MethodDescriptorInfo<'code> {
    pub descriptor: MethodDescriptor<'code>,
    pub stack_effect: isize,
}

impl<'code> ClassInfo<'code> {
    pub fn new(class: &'code Class<'code>) -> Self {
        Self {
            class,
            method_descriptors: FxHashMap::default(),
        }
    }

    pub fn get_method_descriptor(
        &mut self,
        index: Index<NameAndType<'code>>,
    ) -> Result<&MethodDescriptorInfo<'code>, DecodeError> {
        match self.method_descriptors.entry(index) {
            Entry::Occupied(entry) => Ok(entry.into_mut()),
            Entry::Vacant(entry) => {
                let pool = self.class.pool();
                let nat = pool.retrieve(index)?;
                let descriptor = MethodDescriptor::parse(nat.descriptor)?;
                Ok(entry.insert(MethodDescriptorInfo::new(descriptor)))
            }
        }
    }
}

impl<'code> MethodDescriptorInfo<'code> {
    fn new(descriptor: MethodDescriptor<'code>) -> Self {
        let arguments_size: usize = descriptor.parameters().map(type_descriptor_width).sum();

        // For the return type in particular, we could check whether the method descriptor ends
        // with `)V`, `)D`, `)J`, or anything else. But we also have to check argument
        // categories, which cannot be computed that easily without parsing, so let's bite the
        // bullet. This is cached anyway, so the performance doesn't matter as much.
        let return_size = descriptor
            .return_type()
            .map(type_descriptor_width)
            .unwrap_or(0);

        Self {
            descriptor,
            stack_effect: return_size as isize - arguments_size as isize,
        }
    }
}

fn type_descriptor_width(descriptor: TypeDescriptor<'_>) -> usize {
    if descriptor.dimensions == 0 && matches!(descriptor.base, BaseType::Double | BaseType::Long) {
        2
    } else {
        1
    }
}
