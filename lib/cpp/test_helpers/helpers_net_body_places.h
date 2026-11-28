#pragma once

#include <gtest/gtest.h>

#include <array>
#include <format>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

struct NetBodyPlace {
  std::string_view name;
  std::string_view head;
  std::string_view open;
  std::string_view close;
  std::string_view tail;
};

inline constexpr std::array<NetBodyPlace, 5> kNetBodyPlaces = {{
    {"module", "module top;\n", "", "", "endmodule\n"},
    {"interface", "interface host;\n", "", "",
     "endinterface\nmodule top;\n  host h();\nendmodule\n"},
    {"program", "program host;\n", "", "",
     "endprogram\nmodule top;\n  host h();\nendmodule\n"},
    {"if generate block", "module top;\n", "  if (1) begin : g\n", "  end\n",
     "endmodule\n"},
    {"loop generate block", "module top;\n",
     "  for (genvar k = 0; k < 1; k++) begin : g\n", "  end\n", "endmodule\n"},
}};

inline void ExpectPrintedInEveryNetBodyPlace(std::string_view declarations,
                                             std::string_view body,
                                             std::string_view printed) {
  for (const NetBodyPlace& place : kNetBodyPlaces) {
    SCOPED_TRACE(place.name);
    SimFixture f;
    EXPECT_EQ(RunCapture(std::format("{}{}{}{}{}{}", place.head, declarations,
                                     place.open, body, place.close, place.tail),
                         f),
              printed);
  }
}
