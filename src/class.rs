use bitvec::BitArr;
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
use thiserror::Error;

// Acts as a repository of information cached for a class to optimize method decompilation.
pub struct ClassInfo<'code> {
    class: &'code Class<'code>,
    method_descriptors: FxHashMap<Index<NameAndType<'code>>, MethodDescriptorInfo<'code>>,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("Method descriptor for {name} is invalid: {error}")]
    MethodDescriptor {
        error: MethodDescriptorError,
        name: String,
    },
}

#[derive(Debug, Error)]
pub enum MethodDescriptorError {
    #[error("Method has too many parameters")]
    TooManyParameters,
}

pub struct MethodDescriptorInfo<'code> {
    pub descriptor: MethodDescriptor<'code>,
    pub stack_effect: isize,
    pub parameter_sizes: ParameterSizes,
}

// Since the only valid sizes are 1 and 2, we can store sizes as a bit array. This removes
// an allocation and speeds up `invoke*` instruction handling.
pub struct ParameterSizes {
    /// 0 indicates a category-1 type, 1 indicates a category-2 type. JVM allows 255 parameters per
    /// method at most, pad this to 256 for clean code.
    bits: BitArr!(for 256),
    /// Number of parameters.
    len: usize,
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
    ) -> Result<&MethodDescriptorInfo<'code>, Error> {
        match self.method_descriptors.entry(index) {
            Entry::Occupied(entry) => Ok(entry.into_mut()),
            Entry::Vacant(entry) => {
                let pool = self.class.pool();
                let nat = pool.retrieve(index)?;
                let descriptor = MethodDescriptor::parse(nat.descriptor)?;
                let info = MethodDescriptorInfo::try_parse(descriptor).map_err(|error| {
                    Error::MethodDescriptor {
                        error,
                        name: nat.name.display().to_string(),
                    }
                })?;
                Ok(entry.insert(info))
            }
        }
    }
}

impl<'code> MethodDescriptorInfo<'code> {
    fn try_parse(descriptor: MethodDescriptor<'code>) -> Result<Self, MethodDescriptorError> {
        let mut parameter_sizes = ParameterSizes {
            bits: Default::default(),
            len: 0,
        };
        for param in descriptor.parameters() {
            if parameter_sizes.len >= parameter_sizes.bits.len() {
                return Err(MethodDescriptorError::TooManyParameters);
            }
            parameter_sizes
                .bits
                .set(parameter_sizes.len, type_descriptor_width(param) == 2);
            parameter_sizes.len += 1;
        }

        let total_parameters_size = parameter_sizes.len + parameter_sizes.bits.count_ones();

        // For the return type in particular, we could check whether the method descriptor ends with
        // `)V`, `)D`, `)J`, or anything else. But we also have to check argument categories, which
        // cannot be computed that easily without parsing, so let's bite the bullet. This is cached
        // anyway, so the performance doesn't matter as much.
        let return_size = descriptor
            .return_type()
            .map(type_descriptor_width)
            .unwrap_or(0);

        Ok(Self {
            descriptor,
            stack_effect: return_size as isize - total_parameters_size as isize,
            parameter_sizes,
        })
    }
}

impl ParameterSizes {
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = usize> + ExactSizeIterator {
        self.bits[..self.len]
            .iter()
            .map(|is_double| if *is_double { 2 } else { 1 })
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

fn type_descriptor_width(descriptor: TypeDescriptor<'_>) -> usize {
    if descriptor.dimensions == 0 && matches!(descriptor.base, BaseType::Double | BaseType::Long) {
        2
    } else {
        1
    }
}
