theorem facade_new (value : U64) : __NEW__ value = counter_new value := by rfl

theorem facade_read (owner : NativeResourceArc Counter) :
    __READ__ owner = counter_read owner := by rfl

theorem facade_decoded (owner : NativeResourceArc Counter) (request : decoding.Request) (enabled : Bool) :
    __DECODED__ owner request enabled = decoding.counter_decoded owner request enabled := by rfl

theorem facade_first (request : decoding.Request) (owner : NativeResourceArc Counter) :
    __FIRST__ request owner = decoding.counter_decoded owner request true := by rfl
