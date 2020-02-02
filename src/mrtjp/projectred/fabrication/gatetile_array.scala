package mrtjp.projectred.fabrication

trait TArrayGateICTile extends RedstoneGateICTile with IRedwireICPart with IWireICTile with ISEWireTile
{
    def getLogicArray = getLogic[TArrayGateTileLogic[TArrayGateICTile]]

    def getStateRegister(r:Int, linker:ISELinker):Int =  linker.getWirenetOutputRegister(pos, toAbsolute(r))

    override def isNetOutput(r:Int):Boolean =
    {
        if (maskConnects(r)) getStraight(r) match {
            case gate:IRedwireICGate =>
                if(gate.canInputFrom(rotFromStraight(r))) return true
            case _ =>
        }
        false
    }

    override def isNetInput(r:Int):Boolean =
    {
        if (maskConnects(r)) getStraight(r) match {
            case gate:IRedwireICGate =>
                if (gate.canOutputTo(rotFromStraight(r))) return true
            case _ =>
        }
        false
    }

    override def getConnType(r:Int) = getLogicArray.getConnType(r)

    override def getInputColourMask(r:Int) = getLogicArray.getInputColourMask(r)
    override def getOutputColourMask(r:Int) = getLogicArray.getOutputColourMask(r)

    override def getPropMask(r:Int) = getLogicArray.getPropMask(r)

    override def isConnected(r:Int) = maskConnects(r)

    override def buildWireNet(r:Int) = {
        val wireNet = new WireNet(tileMap, pos, getPropMask(r))
        wireNet.calculateNetwork()
        wireNet
    }

    override def cacheStateRegisters(linker:ISELinker){}
}

trait TArrayGateTileLogic[T <: TArrayGateICTile] extends RedstoneGateTileLogic[T]
{
    override def canConnectTo(gate:T, part:ICTile, r:Int) = part match {
        case re:IRedwireICPart if canConnectRedwire(gate, r) => true
        case pc:IRedwireICGate if canConnectRedwire(gate, r) => true
        case _ => super.canConnectTo(gate, part, r)
    }

    def canConnectRedwire(gate:T, r:Int):Boolean = canConnectRedwire(gate.shape, r)
    def canConnectRedwire(shape:Int, r:Int):Boolean = (redwireMask(shape)&1<<r) != 0

    def redwireMask(shape:Int):Int

    def getConnType(r:Int):Int
    def getInputColourMask(r:Int):Int
    def getOutputColourMask(r:Int):Int
    def getPropMask(r:Int):Int
}

class ArrayGateICTile extends RedstoneGateICTile with TComplexGateICTile with TArrayGateICTile
{
    var logic:ArrayGateTileLogic = null

    override def assertLogic()
    {
        if (logic == null) logic = ArrayGateTileLogic.create(this, subID)
    }

    override def getLogic[T]:T = logic.asInstanceOf[T]

    override def getPartType = ICTileDefs.ArrayGate
}

object ArrayGateTileLogic
{
    import mrtjp.projectred.fabrication.{ICGateDefinition => defs}

    def create(gate:ArrayGateICTile, subID:Int):ArrayGateTileLogic = subID match
    {
        case defs.NullCell.ordinal => new NullCell(gate)
        case defs.InvertCell.ordinal => new InvertCell(gate)
        case defs.BufferCell.ordinal => new BufferCell(gate)
        case defs.ANDCell.ordinal => new ANDCell(gate)
        case _ => throw new IllegalArgumentException("Invalid gate subID: "+subID)
    }
}

abstract class ArrayGateTileLogic(val gate:ArrayGateICTile) extends RedstoneGateTileLogic[ArrayGateICTile] with TComplexGateTileLogic[ArrayGateICTile] with TArrayGateTileLogic[ArrayGateICTile]

abstract class ArrayGateTileLogicCrossing(gate:ArrayGateICTile) extends ArrayGateTileLogic(gate)
{
    override def redwireMask(shape:Int) = 0xF

    override def getConnType(r:Int) = 0

    override def getInputColourMask(r:Int) = 0xFFFF
    override def getOutputColourMask(r:Int) = 0xFFFF

    override def getPropMask(r:Int) = if (r%2 == 0) 0x5 else 0xA

    val inputRegs = Array(-1, -1, -1, -1)
    val outputRegs = Array(-1, -1, -1, -1)
    val stateRegs = Array(-1, -1, -1, -1)

    def cacheIORegisters(linker:ISELinker)
    {
        for (r <- 0 until 4) {
            inputRegs(r) =
                    if (canInput(gate, r)) gate.getInputRegister(r, linker) else -1
            outputRegs(r) =
                    if (canOutput(gate, r)) gate.getOutputRegister(r, linker) else -1
            stateRegs(r) =
                    if (getPropMask(r) != 0) gate.getStateRegister(r, linker) else -1
        }
//
//        import SEIntegratedCircuit._
//        if (inputRegs.forall(id => id == -1 || id == REG_ZERO))
//            linker.getLogger.logWarning(Seq(gate.pos), "gate has no inputs")
//        if (outputRegs.forall(id => id == -1 || id == REG_ZERO))
//            linker.getLogger.logWarning(Seq(gate.pos), "gate has no outputs")
    }

    protected def pullInput(mask:Int) = //Pull the input from the sim engine
    {
        var input = 0
        for (r <- 0 until 4) if ((mask&1<<r) != 0) {
            if (gate.editor.simEngineContainer.simEngine.getRegVal[Byte](inputRegs(r)) > 0) input |= 1<<r
        }
        input
    }

    protected def pullOutput(mask:Int) = //Pull the output form the sim engine
    {
        var output = 0
        for (r <- 0 until 4) if ((mask&1<<r) != 0) {
            if (gate.editor.simEngineContainer.simEngine.getRegVal[Byte](outputRegs(r)) > 0) output |= 1<<r
        }
        output
    }

    protected def pullWireState(mask:Int) = //Pull the raw wire state from the sim engine
    {
        var state = 0
        for (r <- 0 until 4) if ((mask&1<<r) != 0) {
            if (gate.editor.simEngineContainer.simEngine.getRegVal[Byte](stateRegs(r)) > 0) state |= 1<<r
        }
        state
    }

    def pullIOStateFromSim()
    {
        val oldState = gate.state
        val wireState = pullWireState(0xF)
        var newState = pullInput(inputMask(gate.shape))&0xF | pullOutput(outputMask(gate.shape))<<4
        newState |= wireState | wireState<<4

        if (oldState != newState) {
            gate.setState(newState)
            gate.sendStateUpdate()
        }
    }

    override def allocateOrFindRegisters(gate:ArrayGateICTile, linker:ISELinker)
    {
        cacheIORegisters(linker)
        allocInternalRegisters(linker)
    }

    override def onRegistersChanged(gate:ArrayGateICTile, regIDs:Set[Int])
    {
        pullIOStateFromSim()
    }

    def allocInternalRegisters(linker:ISELinker)
}

class NullCell(gate:ArrayGateICTile) extends ArrayGateTileLogicCrossing(gate)
{
    override def allocInternalRegisters(linker:ISELinker){}

    override def declareOperations(gate:ArrayGateICTile, linker:ISELinker){}
}

// Crossing array gate with logic
abstract class LogicCell(gate:ArrayGateICTile) extends NullCell(gate)
{
    /* For reference:
     *   Bit 0 - North 
     *   Bit 1 - East
     *   Bit 2 - South 
     *   Bit 3 - West
     */
    override def outputMask(shape:Int) = 0xA
    override def inputMask(shape:Int) = 0x5
    
    def getLogicOp(inputs:Array[Int], outputs:Array[Int]):ISEGate
    
    override def declareOperations(gate:ArrayGateICTile, linker:ISELinker)
    {
        val crossing = gate.getLogic[ArrayGateTileLogicCrossing]
      
        val logic = getLogicOp(crossing.inputRegs, crossing.outputRegs)
        linker.addGate(linker.allocateGateID(Set(gate.pos)), logic,
            crossing.inputRegs.filter(_ != -1),
            crossing.outputRegs.filter(_ != -1))
    }
}

class InvertCell(gate:ArrayGateICTile) extends LogicCell(gate)
{
    override def getLogicOp(inputs:Array[Int], outputs:Array[Int]):ISEGate =
    {
        val inIDs = Seq(inputs(0), inputs(2))
        val outIDs = Seq(outputs(1), outputs(3))
        
        new ISEGate {
            override def compute(ic:SEIntegratedCircuit) {
                val outVal = (if (inIDs.exists(ic.getRegVal(_) != 0)) 0 else 1).toByte
                outIDs.foreach(ic.queueRegVal[Byte](_, outVal))
            }
        }
    }
}

class BufferCell(gate:ArrayGateICTile) extends LogicCell(gate)
{
    override def getLogicOp(inputs:Array[Int], outputs:Array[Int]):ISEGate =
    {
        val inIDs = Seq(inputs(0), inputs(2))
        val outIDs = Seq(outputs(1), outputs(3))
        
        new ISEGate {
            override def compute(ic:SEIntegratedCircuit) {
                val outVal = (if (inIDs.exists(ic.getRegVal(_) != 0)) 1 else 0).toByte
                outIDs.foreach(ic.queueRegVal[Byte](_, outVal))
            }
        }
    }
}

abstract class ThroughLogicCell(gate:ArrayGateICTile) extends ArrayGateTileLogicCrossing(gate) with TArrayGateTileLogic[ArrayGateICTile]
{
    override def getPropMask(r:Int) = if (r%2 == 0) 0 else 0xA
    
    override def allocInternalRegisters(linker:ISELinker){}

    override def inputMask(shape:Int) = 0xE
    
    override def outputMask(shape:Int) = 0x1
    
    override def pullIOStateFromSim()
    {
        val oldState = gate.state
        val wireState = pullWireState(0xA)
        var newState = pullInput(inputMask(gate.shape))&0xF | pullOutput(outputMask(gate.shape))<<4
        newState |= wireState | wireState<<4

        if (oldState != newState) {
            gate.setState(newState)
            gate.sendStateUpdate()
        }
    }
}

class ANDCell(gate:ArrayGateICTile) extends ThroughLogicCell(gate)
{
    
    override def declareOperations(gate:ArrayGateICTile, linker:ISELinker)
    {
        val through = gate.getLogic[ThroughLogicCell]
        
        val wireInputs = Seq(through.inputRegs(1), through.inputRegs(3))
        val dataInput = through.inputRegs(2)
        val dataOutput = through.outputRegs(0)
        
        val logic = new ISEGate {
            override def compute(ic:SEIntegratedCircuit) {
                ic.queueRegVal[Byte](dataOutput, if (wireInputs.exists(ic.getRegVal(_) != 0)) ic.getRegVal(dataInput) else 0)
            }
        }
        
        linker.addGate(linker.allocateGateID(Set(gate.pos)), logic,
            wireInputs++Seq(dataInput),
            Seq(dataOutput))
    }
}