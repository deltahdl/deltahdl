#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>

#include "common/packed_range.h"
#include "parser/ast_type.h"

namespace delta {

// §6.18: what a design records about each name a typedef declares, under the
// name's key, filled by PopulateTypeWidths (elaborator_type_facts.cpp) from
// the elaborator's typedef table, which a simulator does not have. RtlirDesign
// carries these as its own; they are kept apart from rtlir.h, which stands near
// the size the assert-no-oversized-source-files job fails at.
struct RtlirTypedefFacts {
  std::unordered_map<std::string_view, uint32_t> type_widths;
  // §6.18: an object declared with the name has the type the name stands for,
  // and the width beside this cannot say what that is: EvalTypeWidth answers 0
  // for a string, an event, a class handle and a type it could not size alike,
  // so a simulator asking the width alone cannot tell `typedef string s_t` from
  // a name it never saw. The resolved kind is recorded here for every name the
  // typedef table holds, chased through a chain of names to the kind at its
  // end, so the three declaration paths can ask what a name stands for rather
  // than reading DataType::kind and finding kNamed.
  std::unordered_map<std::string_view, DataTypeKind> type_kinds;
  // §6.11.1 makes byte, shortint, int, integer and longint signed by default,
  // and the `signed` keyword makes any of them signed explicitly; neither is
  // recoverable from the width or from the kind alone -- `logic signed [7:0]`
  // and `logic [7:0]` are one kind and one width. Recorded here for the same
  // reason and by the same walk, since a simulator asking IsSignedType of a
  // name has no typedef map to resolve it through.
  std::unordered_map<std::string_view, bool> type_signed;
  // §7.2.1: the resolved declaration of every packed struct or union a typedef
  // names. The three maps above say what a name stands for -- how wide, what
  // kind, signed or not -- and none of them says what is inside it, which is
  // what a member select of a value held under that type has to ask: `p.b`
  // names a run of bits of `p` and the offset of that run is a fact about
  // `pair_t`. A simulator has no typedef table to resolve the name through, and
  // the layout it does register is keyed by the name of a variable, so a value
  // held anywhere else -- a class property (§8.3) -- had nothing to ask at all.
  // Each entry is an arena-owned copy with its nested aggregate members
  // resolved, so it outlives the elaborator that built it.
  std::unordered_map<std::string_view, const DataType*> type_layouts;
  // §6.19 with §6.18: the enumeration declaration every typedef name standing
  // for an enumeration resolves to, under the typedef's key -- the bare name
  // for a module's or an imported one, "P::name" for a package's (§26.3) and
  // "C::name" for a class's (§8.23) -- as the elaborator's typedef table holds
  // it. §6.19.5 declares its methods on the enumeration type, and the
  // simulator, which registers a module's enumerations from RtlirModule's
  // enum_types alone, had no members to answer with for a property declared
  // with a class's or a package's typedef (RegisterDesignEnumTypes in
  // src/simulator/lowerer_data_init.cpp). Each entry is an arena-owned copy,
  // so it outlives the elaborator that built it; the member values fold in
  // the simulator against RtlirDesign::unit_constants.
  std::unordered_map<std::string_view, const DataType*> type_enums;
  // §11.5.1 with §6.18: the packed range the type a name stands for was
  // declared with, as written, for the names standing for a vector of one
  // packed dimension whose bounds fold. `typedef bit [15:10] value_t` is six
  // bits wide, and the width alone addresses it as [5:0], so `v[13:10]` of a
  // `value_t v` declared inside a procedure or a subroutine body -- where the
  // declaration's DataType is the name and carries no dimension of its own --
  // read four bits that are outside a six-bit vector. Recorded only where the
  // bounds fold to constants and the type has one packed dimension; a name
  // nothing here records is addressed as [width-1:0], as before.
  std::unordered_map<std::string_view, PackedRange> type_ranges;
  // §6.18 with §8.3: the name at the end of the chain of typedefs a name
  // stands for, recorded for the names whose chain ends in a name the typedef
  // table does not resolve -- a class. `typedef C T;` makes T the class C
  // (§8.25.1's default specialization for a parameterized C), and a simulator
  // that knows a class by its declared name alone has this to find the class
  // a typedef name denotes, for `T::p` and `T obj`.
  std::unordered_map<std::string_view, std::string_view> type_targets;
  // §25.9 with §6.18: the interface at the end of the chain of typedefs a name
  // stands for, recorded for the names whose chain ends in a virtual interface
  // type, `typedef virtual bus vbus_t;` making vbus_t's `bus`. type_kinds says
  // only that the name is a virtual interface, and a simulator modelling `v.cb`
  // for a var `vbus_t v` has to know which interface's clocking blocks `cb` is
  // among (§37.48).
  std::unordered_map<std::string_view, std::string_view> type_interfaces;
};

}  // namespace delta
