Ionia/Base/base.vo Ionia/Base/base.glob Ionia/Base/base.v.beautified Ionia/Base/base.required_vo: Ionia/Base/base.v 
Ionia/Base/base.vos Ionia/Base/base.vok Ionia/Base/base.required_vos: Ionia/Base/base.v 
Ionia/Base/fin.vo Ionia/Base/fin.glob Ionia/Base/fin.v.beautified Ionia/Base/fin.required_vo: Ionia/Base/fin.v Ionia/Base/base.vo
Ionia/Base/fin.vos Ionia/Base/fin.vok Ionia/Base/fin.required_vos: Ionia/Base/fin.v Ionia/Base/base.vos
Ionia/Base/fle.vo Ionia/Base/fle.glob Ionia/Base/fle.v.beautified Ionia/Base/fle.required_vo: Ionia/Base/fle.v Ionia/Base/base.vo
Ionia/Base/fle.vos Ionia/Base/fle.vok Ionia/Base/fle.required_vos: Ionia/Base/fle.v Ionia/Base/base.vos
Ionia/Base/finfle.vo Ionia/Base/finfle.glob Ionia/Base/finfle.v.beautified Ionia/Base/finfle.required_vo: Ionia/Base/finfle.v Ionia/Base/fin.vo Ionia/Base/fle.vo
Ionia/Base/finfle.vos Ionia/Base/finfle.vok Ionia/Base/finfle.required_vos: Ionia/Base/finfle.v Ionia/Base/fin.vos Ionia/Base/fle.vos
Ionia/Base/vector.vo Ionia/Base/vector.glob Ionia/Base/vector.v.beautified Ionia/Base/vector.required_vo: Ionia/Base/vector.v Ionia/Base/finfle.vo
Ionia/Base/vector.vos Ionia/Base/vector.vok Ionia/Base/vector.required_vos: Ionia/Base/vector.v Ionia/Base/finfle.vos
Ionia/Progress/data.vo Ionia/Progress/data.glob Ionia/Progress/data.v.beautified Ionia/Progress/data.required_vo: Ionia/Progress/data.v Ionia/Base/vector.vo
Ionia/Progress/data.vos Ionia/Progress/data.vok Ionia/Progress/data.required_vos: Ionia/Progress/data.v Ionia/Base/vector.vos
Ionia/Progress/command.vo Ionia/Progress/command.glob Ionia/Progress/command.v.beautified Ionia/Progress/command.required_vo: Ionia/Progress/command.v Ionia/Progress/data.vo
Ionia/Progress/command.vos Ionia/Progress/command.vok Ionia/Progress/command.required_vos: Ionia/Progress/command.v Ionia/Progress/data.vos
Ionia/Progress/rule.vo Ionia/Progress/rule.glob Ionia/Progress/rule.v.beautified Ionia/Progress/rule.required_vo: Ionia/Progress/rule.v Ionia/Progress/command.vo
Ionia/Progress/rule.vos Ionia/Progress/rule.vok Ionia/Progress/rule.required_vos: Ionia/Progress/rule.v Ionia/Progress/command.vos
Ionia/NN/tensor.vo Ionia/NN/tensor.glob Ionia/NN/tensor.v.beautified Ionia/NN/tensor.required_vo: Ionia/NN/tensor.v Ionia/Progress/rule.vo
Ionia/NN/tensor.vos Ionia/NN/tensor.vok Ionia/NN/tensor.required_vos: Ionia/NN/tensor.v Ionia/Progress/rule.vos
Ionia/NN/operation.vo Ionia/NN/operation.glob Ionia/NN/operation.v.beautified Ionia/NN/operation.required_vo: Ionia/NN/operation.v Ionia/NN/tensor.vo
Ionia/NN/operation.vos Ionia/NN/operation.vok Ionia/NN/operation.required_vos: Ionia/NN/operation.v Ionia/NN/tensor.vos
Ionia/NN/model.vo Ionia/NN/model.glob Ionia/NN/model.v.beautified Ionia/NN/model.required_vo: Ionia/NN/model.v Ionia/NN/operation.vo
Ionia/NN/model.vos Ionia/NN/model.vok Ionia/NN/model.required_vos: Ionia/NN/model.v Ionia/NN/operation.vos
Ionia/CodeGen/fun2imp.vo Ionia/CodeGen/fun2imp.glob Ionia/CodeGen/fun2imp.v.beautified Ionia/CodeGen/fun2imp.required_vo: Ionia/CodeGen/fun2imp.v Ionia/Progress/rule.vo
Ionia/CodeGen/fun2imp.vos Ionia/CodeGen/fun2imp.vok Ionia/CodeGen/fun2imp.required_vos: Ionia/CodeGen/fun2imp.v Ionia/Progress/rule.vos
Ionia/CodeGen/imp2c.vo Ionia/CodeGen/imp2c.glob Ionia/CodeGen/imp2c.v.beautified Ionia/CodeGen/imp2c.required_vo: Ionia/CodeGen/imp2c.v Ionia/CodeGen/fun2imp.vo
Ionia/CodeGen/imp2c.vos Ionia/CodeGen/imp2c.vok Ionia/CodeGen/imp2c.required_vos: Ionia/CodeGen/imp2c.v Ionia/CodeGen/fun2imp.vos
Ionia/CodeGen/autogen.vo Ionia/CodeGen/autogen.glob Ionia/CodeGen/autogen.v.beautified Ionia/CodeGen/autogen.required_vo: Ionia/CodeGen/autogen.v Ionia/CodeGen/imp2c.vo
Ionia/CodeGen/autogen.vos Ionia/CodeGen/autogen.vok Ionia/CodeGen/autogen.required_vos: Ionia/CodeGen/autogen.v Ionia/CodeGen/imp2c.vos
