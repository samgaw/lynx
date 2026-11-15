theorem facade_new (value : U64) : __NEW__ value = counter_new value := by rfl

theorem facade_read (owner : NativeResourceArc Counter) : __READ__ owner = counter_read owner := by rfl

theorem facade_map (owner : NativeResourceArc Counter) (request : records.MapRequest) :
    __MAP__ owner request = records.update_map owner request := by rfl

theorem facade_struct (owner : NativeResourceArc Counter) (request : records.StructRequest) :
    __STRUCT__ owner request = records.update_struct owner request := by rfl
