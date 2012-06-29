
type SID = Integer
type Message = String

-- data Protocol s a = Protocol { runProtocol :: SID -> Maybe Message -> s -> (a, s, [(s, Protocol s a)]) }

-- fork :: (s, Protocol s a) -> Protocol s a
-- fork = undefined

{- type of interrupts:

   receiving a message
   generating a fresh nonce
   sending a message
   forking
   publishing a signal

-}

data Protocol s a = Protocol { runProtocol :: s -> (a, s) }

type SuspendedProtocol s a = (s, Protocol s a)

data Interrupt msg sig s = 
    Receive (s, msg -> Protocol s (Interrupt msg sig s))
  | Fresh (s, msg -> Protocol s (Interrupt msg sig s))
  | Send msg  (s, Protocol s (Interrupt msg sig s))
  | Fork (s, Protocol s (Interrupt msg sig s)) (s, Protocol s (Interrupt msg sig s))
  | Signal sig (s, Protocol s (Interrupt msg sig s))
  | Done

