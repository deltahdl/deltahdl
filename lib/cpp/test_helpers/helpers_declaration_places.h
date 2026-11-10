#pragma once

#include <gtest/gtest.h>

#include <array>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

struct DeclarationPlace {
  std::string_view name;
  std::string_view head;
  std::string_view tail;
};

inline constexpr std::array<DeclarationPlace, 11> kDeclarationPlaces = {{
    {"module", "module m;\n", "endmodule\n"},
    {"interface", "interface i;\n",
     "endinterface\nmodule m;\n  i u();\nendmodule\n"},
    {"program", "program p;\n", "endprogram\nmodule m;\n  p u();\nendmodule\n"},
    {"checker", "checker c;\n", "endchecker\nmodule m;\n  c u();\nendmodule\n"},
    {"package", "package q;\n",
     "endpackage\nmodule m;\n  import q::*;\nendmodule\n"},
    {"compilation unit", "", "module m;\nendmodule\n"},
    {"generate block", "module m;\n  if (1) begin : g\n", "  end\nendmodule\n"},
    {"class", "class K;\n", "endclass\nmodule m;\n  K k = new;\nendmodule\n"},
    {"function", "module m;\n  function void f();\n",
     "  endfunction\nendmodule\n"},
    {"task", "module m;\n  task t();\n", "  endtask\nendmodule\n"},
    {"block", "module m;\n  initial begin\n", "  end\nendmodule\n"},
}};

inline const DeclarationPlace& PlaceNamed(std::string_view name) {
  for (const auto& place : kDeclarationPlaces) {
    if (place.name == name) return place;
  }
  ADD_FAILURE() << "no place named " << name;
  return kDeclarationPlaces[0];
}

inline std::string InPlace(std::string_view name, std::string_view body) {
  const DeclarationPlace& place = PlaceNamed(name);
  return std::string(place.head) + std::string(body) + std::string(place.tail);
}

inline void ExpectReportedIn(std::initializer_list<std::string_view> names,
                             std::string_view body, std::string_view message,
                             std::string_view at, std::string_view subclause) {
  for (std::string_view name : names) {
    SCOPED_TRACE(name);
    std::string src = InPlace(name, body);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                              LineHolding(src, at), subclause));
  }
}

inline void ExpectReportedOnceIn(std::initializer_list<std::string_view> names,
                                 std::string_view body,
                                 std::string_view message, std::string_view at,
                                 std::string_view subclause) {
  for (std::string_view name : names) {
    SCOPED_TRACE(name);
    std::string src = InPlace(name, body);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                              LineHolding(src, at), subclause));
    EXPECT_EQ(f.diag.ErrorCount(), 1u);
  }
}

inline void ExpectCleanIn(std::initializer_list<std::string_view> names,
                          std::string_view body) {
  for (std::string_view name : names) {
    SCOPED_TRACE(name);
    std::string src = InPlace(name, body);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.has_errors) << src;
  }
}
