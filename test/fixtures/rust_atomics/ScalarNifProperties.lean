theorem facade_new (value : U64) : __NEW__ value = counter_new value := by rfl

theorem facade_read (owner : NativeResourceArc Counter) : __READ__ owner = counter_read owner := by rfl

theorem facade_mixed (owner : NativeResourceArc Counter) (request : scalars.Request) :
    __MIXED__ owner request = scalars.counter_scalar owner request := by rfl

theorem facade_bool (value : scalars.BoolValue) :
    __BOOL__ value = NativeM.ok value.value := by rfl

theorem facade_i8 (value : scalars.I8Value) :
    __I8__ value = NativeM.ok value.value := by rfl

theorem facade_i16 (value : scalars.I16Value) :
    __I16__ value = NativeM.ok value.value := by rfl

theorem facade_i32 (value : scalars.I32Value) :
    __I32__ value = NativeM.ok value.value := by rfl

theorem facade_i64 (value : scalars.I64Value) :
    __I64__ value = NativeM.ok value.value := by rfl

theorem facade_u8 (value : scalars.U8Value) :
    __U8__ value = NativeM.ok value.value := by rfl

theorem facade_u16 (value : scalars.U16Value) :
    __U16__ value = NativeM.ok value.value := by rfl

theorem facade_u32 (value : scalars.U32Value) :
    __U32__ value = NativeM.ok value.value := by rfl

theorem facade_u64 (value : scalars.U64Value) :
    __U64__ value = NativeM.ok value.value := by rfl
