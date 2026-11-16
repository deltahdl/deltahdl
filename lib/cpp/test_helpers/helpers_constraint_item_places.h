#pragma once

#include <cstdint>
#include <string>

enum class ItemPlace : std::uint8_t {
  kClassBlock,
  kOutOfBlock,
  kInline,
  kScope
};

inline constexpr ItemPlace kEveryItemPlace[] = {
    ItemPlace::kClassBlock, ItemPlace::kOutOfBlock, ItemPlace::kInline,
    ItemPlace::kScope};

inline constexpr ItemPlace kItemPlacesBeyondTheClass[] = {
    ItemPlace::kOutOfBlock, ItemPlace::kInline, ItemPlace::kScope};

inline const char* ItemPlaceName(ItemPlace place) {
  switch (place) {
    case ItemPlace::kOutOfBlock:
      return "out-of-block constraint";
    case ItemPlace::kInline:
      return "randomize() with";
    case ItemPlace::kScope:
      return "std::randomize() with";
    default:
      return "class constraint block";
  }
}

inline std::string ScopeItemIn(const std::string& decl, const std::string& args,
                               const std::string& item,
                               const std::string& prefix = "") {
  const std::string kHead = prefix.empty() ? "" : prefix + "\n";
  return kHead + "module t;\n  " + decl +
         "\n"
         "  function int f(); return 1; endfunction\n"
         "  initial begin\n"
         "    void'(std::randomize(" +
         args + ") with { " + item +
         " });\n"
         "  end\n"
         "endmodule\n";
}

inline std::string ItemIn(ItemPlace place, const std::string& decl,
                          const std::string& item,
                          const std::string& prefix = "") {
  const std::string kHead = prefix.empty() ? "" : prefix + "\n";
  switch (place) {
    case ItemPlace::kOutOfBlock:
      return kHead + "class C;\n  " + decl +
             "\n"
             "  constraint k;\n"
             "endclass\n"
             "constraint C::k { " +
             item +
             " }\n"
             "module m; endmodule\n";
    case ItemPlace::kInline:
      return kHead + "class C;\n  " + decl +
             "\n"
             "endclass\n"
             "module t;\n"
             "  initial begin static C o = new; void'(o.randomize() with { " +
             item +
             " }); end\n"
             "endmodule\n";
    case ItemPlace::kScope:
      return ScopeItemIn(decl, "z", item, prefix);
    default:
      return kHead + "class C;\n  " + decl +
             "\n"
             "  function int f(); return 1; endfunction\n"
             "  static int sa[3];\n"
             "  constraint k { " +
             item +
             " }\n"
             "endclass\n"
             "module m; endmodule\n";
  }
}
