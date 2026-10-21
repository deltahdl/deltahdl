#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;

// IEEE 1800-2023 §40.5.1 and §40.5.2: the FSM objects of the model. Each FSM
// the run counts the coverage of (fsm_coverage.cpp) is a vpiFsm object of its
// instance, which vpi_iterate(vpiFsm, instance) reaches, named as §40.4 names
// it: by its fsm_name where a part-select or a concatenation holds its state,
// and by its signal otherwise. Its legal states are its children, which
// vpi_iterate(vpiFsmStates, fsm) reaches and vpi_get_value() reads the
// parameter value of. §40.5.1 names two FSM handle types, and §40.5.2 two
// kinds of FSM object, the FSM and its states, so a state is the second type,
// vpiFsmHandle.
void AttachFsms(const VpiObjectMap& objects, SimContext& ctx,
                const VpiAttachBuild& build);

}  // namespace delta
