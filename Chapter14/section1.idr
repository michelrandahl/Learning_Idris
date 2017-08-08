module Section1

data DoorState = DoorClosed | DoorOpen

data DoorResult = OK | Jammed

data DoorCmd : (door_res : Type) -> DoorState -> (door_res -> DoorState) -> Type where
  Open : DoorCmd DoorResult DoorClosed (\door_res => (case door_res of
                                                           OK => DoorOpen
                                                           Jammed => DoorClosed))
  Close : DoorCmd () DoorOpen (const DoorClosed)
  RingBell : DoorCmd () DoorClosed (const DoorClosed)

  Display : String -> DoorCmd () state (const state)

  Pure  : (door_res : a) -> DoorCmd a (state_fn door_res) state_fn
  (>>=) : DoorCmd a state1 state2_fn ->
          ((door_res : a) -> DoorCmd b (state2_fn door_res) state3_fn) ->
          DoorCmd b state1 state3_fn

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do RingBell
              OK <- Open | Jammed => Display "door is jammed!!"
              Display "welcome in"
              Close

doorProg2 : DoorCmd () DoorClosed (const DoorClosed)
doorProg2 = do RingBell
               OK <- Open | Jammed => Display "door is jammed!"
               Display "welcome in"
               Close
               OK <- Open | Jammed => Display "door is jammed"
               Display "welcome"
               Close

logOpen : DoorCmd DoorResult DoorClosed (\door_res => (case door_res of
                                                            OK => DoorOpen
                                                            Jammed => DoorClosed))
logOpen = do Display "attempting to open door"
             OK <- Open | Jammed => do Display "jammed.."
                                       Pure Jammed
             Display "success"
             Pure OK
