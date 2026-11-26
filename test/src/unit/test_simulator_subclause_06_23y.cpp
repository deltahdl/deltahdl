#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr std::string_view kTypedef = "typedef type(logic [6:0]) t;";

std::string Placed(std::string_view before, std::string_view after) {
  return std::string(before).append(kTypedef).append(after);
}

struct TypedefPlace {
  std::string source;
  std::string_view printed;
};

TEST(TypedefOfADataTypeReferenceSim, TakesTheDataTypeInEachPlace) {
  const TypedefPlace kPlaces[] = {
      {Placed("module m;\n  ",
              "\n  t x;\n  initial $display(\"%0d\", $bits(x));\n"
              "endmodule\n"),
       "7\n"},
      {Placed("",
              "\nmodule m;\n  t x;\n  initial $display(\"%0d\", $bits(x));\n"
              "endmodule\n"),
       "7\n"},
      {Placed("package pk;\n  ",
              "\n  t pv;\nendpackage\nmodule m;\n  pk::t x;\n"
              "  initial $display(\"%0d %0d\", $bits(x), $bits(pk::pv));\n"
              "endmodule\n"),
       "7 7\n"},
      {Placed("interface ifc;\n  ",
              "\n  t x;\nendinterface\nmodule m;\n  ifc i();\n"
              "  initial $display(\"%0d\", $bits(i.x));\nendmodule\n"),
       "7\n"},
      {Placed("program pg;\n  ",
              "\n  t x;\n  initial $display(\"%0d\", $bits(x));\n"
              "endprogram\n"),
       "7\n"},
      {Placed("module m;\n  if (1) begin : g\n    ",
              "\n    t x;\n    initial $display(\"%0d\", $bits(x));\n"
              "  end\nendmodule\n"),
       "7\n"},
      {Placed("class C;\n  ",
              "\n  t x;\nendclass\nmodule m;\n  C c = new;\n  C::t y;\n"
              "  initial $display(\"%0d %0d\", $bits(c.x), $bits(y));\n"
              "endmodule\n"),
       "7 7\n"},
      {Placed("module m;\n  task automatic tk;\n    ",
              "\n    t x;\n    $display(\"%0d\", $bits(x));\n  endtask\n"
              "  initial tk;\nendmodule\n"),
       "7\n"},
      {Placed("module m;\n  function automatic void fn;\n    ",
              "\n    t x;\n    $display(\"%0d\", $bits(x));\n  endfunction\n"
              "  initial fn;\nendmodule\n"),
       "7\n"},
      {Placed("module m;\n  initial begin\n    ",
              "\n    t x;\n    $display(\"%0d\", $bits(x));\n  end\n"
              "endmodule\n"),
       "7\n"},
  };
  for (const TypedefPlace& place : kPlaces) {
    SCOPED_TRACE(place.source);
    SimFixture f;
    EXPECT_EQ(RunCapture(place.source, f), place.printed);
  }
}

TEST(TypedefOfADataTypeReferenceSim, TakesEachKindOfDataType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk; typedef logic [2:0] pt; endpackage\n"
                 "class C; int v = 11; endclass\n"
                 "typedef logic [5:0] base_t;\n"
                 "module m;\n"
                 "  typedef type(real) kt;\n"
                 "  typedef type(byte) at;\n"
                 "  typedef type(bit signed [3:0]) st;\n"
                 "  typedef type(struct packed { logic [2:0] a; logic [1:0] b; "
                 "}) gt;\n"
                 "  typedef type(base_t) nt;\n"
                 "  typedef type(pk::pt) qt;\n"
                 "  typedef type(C) ct;\n"
                 "  kt k;\n"
                 "  at a;\n"
                 "  st s = -1;\n"
                 "  gt p;\n"
                 "  nt n;\n"
                 "  qt q;\n"
                 "  ct c;\n"
                 "  initial begin\n"
                 "    c = new;\n"
                 "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", $bits(k), "
                 "$bits(a),\n"
                 "             $bits(s), s, $bits(p), $bits(n), $bits(q));\n"
                 "    $display(\"%0d\", c.v);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "64 8 4 -1 5 6 3\n11\n");
}

}  // namespace
