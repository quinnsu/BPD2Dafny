/**
 *  Provide state type
 */
module BPMNState{


 /**
     * Captures the possible state of the BPMN.  Normal execution is
     * indicated by RUNNING.  Completed is when the BPMN is completed successfully.
     * Terminated is when the BPMN is terminated by an error.
     * Compensating is when the BPMN is compensating for a failed activity.
     */

datatype State = 
  | Running(process: ProcessObj)
  | Completed(process: ProcessObj, output: Variables)
  | Terminated(process: ProcessObj)
  | Error(process: ProcessObj, errorCode: ErrorCode)
  | Compensating(process: ProcessObj)
}