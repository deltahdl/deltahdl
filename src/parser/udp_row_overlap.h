#pragma once

#include "parser/ast_specify.h"

namespace delta {

bool UdpRowsConflict(const UdpTableRow& a, const UdpTableRow& b);

}  // namespace delta
