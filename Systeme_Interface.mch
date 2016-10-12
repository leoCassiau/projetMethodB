/* Systeme_Interface
 * Author: 
 * Creation date: 12/10/16
 */
MACHINE
    Systeme_Interface
USES
    Systeme
    
OPERATIONS
    
    res <-- demander(pp, ss) = // 
    PRE
        pp : processus &
        ss : services 
    THEN
        //res :=
    END
    
END
