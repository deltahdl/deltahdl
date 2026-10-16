#pragma once

#include <cstdint>

namespace delta {

// §37.3.7: the categories an allocator can place an object into, used to derive
// its vpiAllocScheme. Keeping this separate from the scheme return values lets
// callers describe an allocation in intent ("this came from a frame") and have
// the mapping to the reported scheme live in one place.
enum class VpiAllocKind : std::uint8_t {
  kFrameOrThread,  // allocated with a frame or thread -> Automatic scheme
  kDynamic,        // allocated in dynamic memory (class object) -> Dynamic
  kOther,          // anything else -> the mandated Other default
};

// §37.3.7: map an allocation category to the vpiAllocScheme value that
// vpi_get(vpiAllocScheme) must report. Unrecognized/other allocations fall
// through to kVpiOtherScheme, the scheme the clause gives every other object.
int VpiAllocSchemeFor(VpiAllocKind kind);

}  // namespace delta
