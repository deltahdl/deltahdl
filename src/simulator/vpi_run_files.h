#pragma once

#include <string>
#include <string_view>

#include "simulator/vpi_user.h"

namespace delta {

class SimContext;

PLI_UINT32 VpiRunMcdOpen(SimContext& run, const std::string& name);

PLI_UINT32 VpiRunMcdClose(SimContext& run, PLI_UINT32 mcd);

const std::string* VpiRunFileName(SimContext& run, PLI_UINT32 cd);

void VpiRunMcdWrite(SimContext& run, PLI_UINT32 channel, std::string_view text);

bool VpiRunMcdFlush(SimContext& run, PLI_UINT32 channel);

}  // namespace delta
