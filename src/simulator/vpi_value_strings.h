#pragma once

#include <string>
#include <vector>

#include "common/types.h"
#include "simulator/vpi_user.h"

namespace delta {

// §38.15, Table 38-3: the string formats of vpi_get_value(), each writing the
// text of `v` into `pool` and pointing value->value.str at it.
void GetValueBinStr(const Logic4Vec& v, s_vpi_value* value,
                    std::vector<std::string>& pool);
void GetValueOctStr(const Logic4Vec& v, s_vpi_value* value,
                    std::vector<std::string>& pool);
void GetValueHexStr(const Logic4Vec& v, s_vpi_value* value,
                    std::vector<std::string>& pool);
void GetValueDecStr(const Logic4Vec& v, s_vpi_value* value,
                    std::vector<std::string>& pool);
void GetValueStringVal(const Logic4Vec& v, s_vpi_value* value,
                       std::vector<std::string>& pool);

}  // namespace delta
