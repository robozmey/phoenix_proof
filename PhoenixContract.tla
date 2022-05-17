---- MODULE PhoenixContract ----

EXTENDS Integers, Sequences

CONSTANTS
    BALANCE_LIMIT,
    ADDRESSES,
    MONEY,
    MAX_BLOCK_NUMBER,
    REQUEST_IDS

ASSUMPTION ADDRESSES \subseteq Nat
ASSUMPTION MONEY \subseteq Nat

VARIABLES
    balance,                          \* F
    block_number,                     
    tier_one_addresses,               \* T1
    tier_two_addresses,               \* T2
    delay,                            \* D
    unlock_block,                     \* U
    requests                          \* R

vars == <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests>>

request == \* (id, amount, XrecipientX, creation, initiator)
    REQUEST_IDS 
    \X MONEY 
    \* \X NETWORK_ADDRESSES 
    \X (0..MAX_BLOCK_NUMBER)
    \X tier_two_addresses

TypeOK ==
    /\ balance \in Nat
    /\ block_number \in 0..MAX_BLOCK_NUMBER
    /\ tier_one_addresses \in SUBSET ADDRESSES
    /\ tier_two_addresses \in SUBSET ADDRESSES
    /\ (tier_one_addresses \intersect tier_two_addresses) = {}
    /\ delay \in 0..MAX_BLOCK_NUMBER
    /\ unlock_block \in 0..MAX_BLOCK_NUMBER
    /\ requests 


Init ==
    /\ balance = 0
    /\ block_number = 0
    /\ tier_one_addresses = {0}
    /\ tier_two_addresses = {}
    /\ delay = 3
    /\ unlock_block = 0
    /\ requests = 0

Tick ==
    /\ block_number + 1 <= MAX_BLOCK_NUMBER
    /\ block_number' = block_number + 1
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests>>

--------------------------------------
\* Actions

Deposit(amount) ==
    /\ amount > 0
    /\ balance + amount <= BALANCE_LIMIT
    /\ balance' = balance + amount
    /\ UNCHANGED <<block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests>>

Request(address2, id, amount) ==
    /\ amount > 0
    /\ address2 \in tier_two_addresses
    /\ id
    /\ requests' = requests \union <<id, amount, block_number, address2>>
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>

Withdraw(id) == UNCHANGED vars
    
    
CancelRequest(address1, id) == UNCHANGED vars

CancelAllRequests(address1) ==
    /\ address1 \in tier_one_addresses
    /\ requests' = {}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>

CancelSelfRequest(address2) ==
    /\ address2 \in tier_two_addresses

Lock(address1, new_unlock_block) == UNCHANGED vars
    
AddTierOneAddress(address1, new_address1) == UNCHANGED vars

AddTierTwoAddress(address1, new_address2) == UNCHANGED vars

RemoveTierTwoAddress(address1, remove_address2) == UNCHANGED vars

Next ==
    \/ Tick
    \/ \E amount \in MONEY: 
        Deposit(amount)
    \* \/ \E <<address2, id, amount>> \in ADDRESSES \X REQUEST_IDS \X MONEY:
    \*     Request(address2, id, amount)
    \* \/ \E id \in REQUEST_IDS: 
    \*     Withdraw(id) 
    \* \/ \E <<address1, id>> \in ADDRESSES \X REQUEST_IDS: 
    \*     CancelRequest(address1, id)
    \* \/ \E address1 \in tier_one_addresses: 
    \*     CancelAllRequests(address1) 
    \* \/ \E address2 \in tier_two_addresses: 
    \*     CancelSelfRequest(address2) 
    \* \/ \E <<address1, new_unlock_block>> \in ADDRESSES \X 0..MAX_BLOCK_NUMBER: 
    \*     Lock(address1, new_unlock_block)
    \* \/ \E <<address1, new_address1>> \in ADDRESSES \X ADDRESSES: 
    \*     AddTierOneAddress(address1, new_address1)
    \* \/ \E <<address1, new_address2>> \in ADDRESSES \X ADDRESSES: 
    \*     AddTierTwoAddress(address1, new_address2)
    \* \/ \E <<address1, remove_address2>> \in ADDRESSES \X ADDRESSES: 
    \*     RemoveTierTwoAddress(address1, remove_address2)

Spec == Init /\ [][Next]_vars

\* WF = weak fairness

\* liveness

--------------------------------------

ADDRESSES_const == 0..2
MONEY_const == 0..2
REQUEST_IDS_const == 0..2

====