#pragma once

#include <array>
#include <string>

inline constexpr std::array<const char*, 4> kGenerateForms = {"if", "for",
                                                              "case", "region"};

inline std::string InGenerateForm(const std::string& form,
                                  const std::string& item) {
  if (form == "if") return "  if (1) begin\n    " + item + "\n  end\n";
  if (form == "for") {
    return "  for (genvar i = 0; i < 1; i++) begin\n    " + item + "\n  end\n";
  }
  if (form == "case") {
    return "  case (1) 1: begin\n    " + item + "\n  end endcase\n";
  }
  return "  generate\n    " + item + "\n  endgenerate\n";
}
