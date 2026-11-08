#pragma once

#include <string>
#include <vector>

#include "common/types.h"
#include "simulator/vpi_user.h"

namespace delta {

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
