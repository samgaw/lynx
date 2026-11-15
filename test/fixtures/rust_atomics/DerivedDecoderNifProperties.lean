theorem facade_new (value : U64) : __NEW__ value = counter_new value := by rfl

theorem facade_read (owner : NativeResourceArc Counter) :
    __READ__ owner = counter_read owner := by rfl

theorem facade_tuple (owner : NativeResourceArc Counter) (request : derived.Request) :
    __TUPLE__ owner request = derived.counter_tuple owner request := by rfl
