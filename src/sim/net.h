#pragma once

#include "common/types.h"

#include <cstdint>

namespace delta {

struct Process;

// --- Driver: a single source driving a net ---

struct Driver {
    Logic4Vec driven_value{};
    StrengthVal* strengths = nullptr;
    Process* source = nullptr;
};

// --- Net: a resolved signal with multiple drivers ---

struct Net {
    NetType type = NetType::Wire;
    Logic4Vec value{};
    StrengthVal* strengths = nullptr;
    SmallVec<Driver*> drivers;
};

// --- Resolution functions (IEEE 1800-2023 section 6.5) ---

Logic4Vec resolve_wire(const SmallVec<Driver*>& drivers);
Logic4Vec resolve_wand(const SmallVec<Driver*>& drivers);
Logic4Vec resolve_wor(const SmallVec<Driver*>& drivers);

} // namespace delta
