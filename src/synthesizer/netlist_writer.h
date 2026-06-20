#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "synthesizer/aig.h"

namespace delta {

enum class NetlistFormat : uint8_t {
  kVerilog,
  kBlif,
  kJson,
  kEdif,
};

class NetlistWriter {
 public:
  static std::string WriteBlif(const AigGraph& aig,
                               std::string_view module_name);

  static std::string WriteVerilog(const AigGraph& aig,
                                  std::string_view module_name);

  static std::string WriteJson(const AigGraph& aig,
                               std::string_view module_name);

  static std::string WriteEdif(const AigGraph& aig,
                               std::string_view module_name);

  static std::string Write(const AigGraph& aig, std::string_view module_name,
                           NetlistFormat fmt);
};

}  // namespace delta
