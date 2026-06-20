#pragma once

// Umbrella header for the VPI interface. The declarations were split into the
// topical sub-headers below to keep each file within the repository's per-file
// line limit; they are included here in dependency order so that every existing
// `#include "simulator/vpi.h"` continues to provide the same complete interface
// it always did. Do not reorder these includes - later sub-headers depend on
// types declared in earlier ones, and the PLI typedefs/macros in
// vpi_user_macros.h are intentionally introduced after the delta::VpiContext
// declarations, matching the original single-file ordering.

#include "simulator/vpi_constants.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_user_macros.h"
