include "NodeIdentity.s.dfy"
include "../../Common/Native/Io.s.dfy"

module Concrete_NodeIdentity_i refines Common__NodeIdentity_s {
  import opened Native__Io_s
  export Spec provides NodeIdentity
  export reveals *

  type NodeIdentity = EndPoint
}
