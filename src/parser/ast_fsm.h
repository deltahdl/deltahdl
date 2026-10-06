#pragma once

#include <string_view>
#include <vector>

namespace delta {

// §40.4: a finite state machine the FSM pragmas of a module definition
// identify. §40.4 names three things that make one up: the state register or
// expression, the next-state register, and the legal states. The enumeration
// name is what ties the pragmas naming them together into one FSM (§40.4.1).
struct FsmDecl {
  // §40.4.1 to §40.4.3: the signal holding the current state, or, for a
  // concatenation, every signal it lists, most significant first.
  std::vector<std::string_view> state_signals;
  // §40.4.2: the bounds of the part-select of the one signal that holds the
  // current state, where a part-select does.
  bool has_part_select = false;
  int msb = 0;
  int lsb = 0;
  // §40.4.2 and §40.4.3: the name a part-select or concatenation FSM is
  // reported under; empty for a whole signal, which names its FSM itself.
  std::string_view fsm_name;
  // §40.4.1: the enumeration name of the FSM.
  std::string_view enum_name;
  // §40.4.6: the parameters naming the FSM's legal states, in declaration
  // order: those of every parameter declaration tagged with `enum_name`.
  std::vector<std::string_view> states;
};

}  // namespace delta
