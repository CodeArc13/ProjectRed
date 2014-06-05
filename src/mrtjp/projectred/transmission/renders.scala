package mrtjp.projectred.transmission

import net.minecraftforge.client.IItemRenderer
import net.minecraft.item.ItemStack
import net.minecraftforge.client.IItemRenderer.{ItemRendererHelper, ItemRenderType}
import codechicken.lib.render.{CCRenderState, TextureUtils}
import codechicken.lib.vec.{Transformation, Translation, Scale}
import net.minecraft.util.IIcon

trait TWireItemRenderCommon extends IItemRenderer
{
    def handleRenderType(item:ItemStack, rtype:ItemRenderType) = true

    def shouldUseRenderHelper(rtype:ItemRenderType, item:ItemStack, helper:ItemRendererHelper) = true

    def renderWireInventory(meta:Int, x:Float, y:Float, z:Float, scale:Float)
    {
        val wdef = WireDef.values(meta)
        if (wdef == null) return
        TextureUtils.bindAtlas(0)
        CCRenderState.reset()
        CCRenderState.useNormals = true
        CCRenderState.pullLightmap()
        CCRenderState.setColour(wdef.itemColour)
        CCRenderState.startDrawing()

        doRender(wdef.thickness, new Scale(scale).`with`(new Translation(x, y, z)), wdef.wireSprites(0))

        CCRenderState.draw()
    }

    def doRender(thickness:Int, t:Transformation, icon:IIcon)
}

object WireItemRenderer extends TWireItemRenderCommon
{
    override def renderItem(rtype:ItemRenderType, item:ItemStack, data:AnyRef*)
    {
        val damage = item.getItemDamage
        import ItemRenderType._
        rtype match
        {
            case ENTITY => renderWireInventory(damage, -0.3f, 0f, -0.3f, 0.6f)
            case EQUIPPED => renderWireInventory(damage, 0f, .0f, 0f, 1f)
            case EQUIPPED_FIRST_PERSON => renderWireInventory(damage, 1f, -0.6f, -0.4f, 2f)
            case INVENTORY => renderWireInventory(damage, 0f, -0.1f, 0f, 1f)
            case _ =>
        }
    }

    override def doRender(thickness:Int, t:Transformation, icon:IIcon)
    {
        RenderWire.renderInv(thickness, t, icon)
    }
}

object FramedWireItemRenderer extends TWireItemRenderCommon
{
    override def renderItem(rtype:ItemRenderType, item:ItemStack, data:AnyRef*)
    {
        val damage = item.getItemDamage
        import ItemRenderType._
        rtype match
        {
            case ENTITY => renderWireInventory(damage, -0.5f, 0f, -0.5f, 1f)
            case EQUIPPED => renderWireInventory(damage, 0f, 0f, 0f, 1f)
            case EQUIPPED_FIRST_PERSON => renderWireInventory(damage, 1f, -0.6f, -0.4f, 2f)
            case INVENTORY => renderWireInventory(damage, 0f, -0.1f, 0f, 1f)
            case _ =>
        }
    }

    override def doRender(thickness:Int, t:Transformation, icon:IIcon)
    {
        RenderFramedWire.renderInv(thickness, t, icon)
    }
}